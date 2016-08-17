{-|
Copyright  :  (C) 2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

A type checker plugin for GHC that can derive \"complex\" @KnownNat@
constraints from other simple/variable @KnownNat@ constraints. i.e. without
this plugin, you must have both a @KnownNat n@ and a @KnownNat (n+2)@
constraint in the type signature of the following function:

@
f :: forall n . (KnownNat n, KnownNat (n+2)) => Proxy n -> Integer
f _ = natVal (Proxy :: Proxy n) + natVal (Proxy :: Proxy (n+2))
@

Using the plugin you can omit the @KnownNat (n+2)@ constraint:

@
f :: forall n . KnownNat n => Proxy n -> Integer
f _ = natVal (Proxy :: Proxy n) + natVal (Proxy :: Proxy (n+2))
@

The plugin can derive @KnownNat@ constraints for types consisting of:

* Type variables, when there is a corresponding @KnownNat@ constraint
* Type-level naturals
* Applications of the arithmetic expression: @{+,-,*,^}@
* Type functions, when there is either:
  * a matching given @KnownNat@ constraint; or
  * a corresponding @KnownNat\<N\>@ instance for the type function

To elaborate the latter points, given the type family @Min@:

@
type family Min (a :: Nat) (b :: Nat) :: Nat where
  Min 0 b = 0
  Min a b = If (a <=? b) a b
@

the plugin can derive a @KnownNat (Min x y + 1)@ constraint given only a
@KnownNat (Min x y)@ constraint:

@
g :: forall x y . (KnownNat (Min x y)) => Proxy x -> Proxy y -> Integer
g _ _ = natVal (Proxy :: Proxy (Min x y + 1))
@

And, given the type family @Max@:

@
type family Max (a :: Nat) (b :: Nat) :: Nat where
  Max 0 b = b
  Max a b = If (a <=? b) b a
@

and corresponding @KnownNat2@ instance:

@
instance (KnownNat a, KnownNat b) => KnownNat2 \"TestFunctions.Max\" a b where
  type KnownNatF2 \"TestFunctions.Max\" = MaxSym2
  natSing2 = let x = natVal (Proxy @ a)
                 y = natVal (Proxy @ b)
                 z = max x y
             in  SNatKn z
  \{\-# INLINE natSing2 \#-\}
@

the plugin can derive a @KnownNat (Max x y + 1)@ constraint given only a
@KnownNat x@ and @KnownNat y@ constraint:

@
h :: forall x y . (KnownNat x, KnownNat y) => Proxy x -> Proxy y -> Integer
h _ _ = natVal (Proxy :: Proxy (Max x y + 1))
@

To use the plugin, add the

@
OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver
@

Pragma to the header of your file.

-}

{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns  #-}

{-# LANGUAGE Trustworthy   #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module GHC.TypeLits.KnownNat.Solver (plugin) where

-- external
import Control.Arrow                ((&&&), first)
import Control.Monad.Trans.Maybe    (MaybeT (..))
import Data.Maybe                   (catMaybes,mapMaybe)
import GHC.TcPluginM.Extra          (lookupModule, lookupName, newWanted,
                                     tracePlugin)
import GHC.TypeLits.Normalise.SOP   (SOP (..), Product (..), Symbol (..))
import GHC.TypeLits.Normalise.Unify (CType (..),normaliseNat,reifySOP)

-- GHC API
import Class      (Class, classMethods, className, classTyCon)
import FamInst    (tcInstNewTyCon_maybe)
import FastString (fsLit)
import Id         (idType)
import InstEnv    (instanceDFunId,lookupUniqueInstEnv)
import Module     (mkModuleName, moduleName, moduleNameString)
import Name       (nameModule_maybe, nameOccName)
import OccName    (mkTcOcc, occNameString)
import Plugins    (Plugin (..), defaultPlugin)
import PrelNames  (knownNatClassName)
import TcEvidence (EvTerm (..), mkEvCast, mkTcSymCo, mkTcTransCo)
import TcPluginM  (TcPluginM, tcLookupClass, getInstEnvs, zonkCt)
import TcRnTypes  (Ct, TcPlugin(..), TcPluginResult (..), ctEvidence, ctEvPred,
                   ctEvTerm, ctLoc, isWanted, mkNonCanonical)
import TcTypeNats (typeNatAddTyCon, typeNatSubTyCon)
import Type       (PredTree (ClassPred), PredType, classifyPredType, dropForAlls,
                   funResultTy, mkNumLitTy, mkStrLitTy, mkTyConApp, piResultTys,
                   splitFunTys, splitTyConApp_maybe, tyConAppTyCon_maybe)
import TyCon      (tyConName)
import TyCoRep    (Type (..))
import Var        (DFunId)

-- | Classes and instances from "GHC.TypeLits.KnownNat"
type KnownNatDefs = Int -> Maybe Class -- ^ KnownNatN class

-- | KnownNat constraints
type KnConstraint = (Ct    -- The constraint
                    ,Class -- KnownNat class
                    ,Type  -- The argument to KnownNat
                    )

{-|
A type checker plugin for GHC that can derive \"complex\" @KnownNat@
constraints from other simple/variable @KnownNat@ constraints. i.e. without
this plugin, you must have both a @KnownNat n@ and a @KnownNat (n+2)@
constraint in the type signature of the following function:

@
f :: forall n . (KnownNat n, KnownNat (n+2)) => Proxy n -> Integer
f _ = natVal (Proxy :: Proxy n) + natVal (Proxy :: Proxy (n+2))
@

Using the plugin you can omit the @KnownNat (n+2)@ constraint:

@
f :: forall n . KnownNat n => Proxy n -> Integer
f _ = natVal (Proxy :: Proxy n) + natVal (Proxy :: Proxy (n+2))
@

The plugin can derive @KnownNat@ constraints for types consisting of:

* Type variables, when there is a corresponding @KnownNat@ constraint
* Type-level naturals
* Applications of the arithmetic expression: @{+,-,*,^}@
* Type functions, when there is either:
  * a matching given @KnownNat@ constraint; or
  * a corresponding @KnownNat\<N\>@ instance for the type function

To elaborate the latter points, given the type family @Min@:

@
type family Min (a :: Nat) (b :: Nat) :: Nat where
  Min 0 b = 0
  Min a b = If (a <=? b) a b
@

the plugin can derive a @KnownNat (Min x y + 1)@ constraint given only a
@KnownNat (Min x y)@ constraint:

@
g :: forall x y . (KnownNat (Min x y)) => Proxy x -> Proxy y -> Integer
g _ _ = natVal (Proxy :: Proxy (Min x y + 1))
@

And, given the type family @Max@:

@
type family Max (a :: Nat) (b :: Nat) :: Nat where
  Max 0 b = b
  Max a b = If (a <=? b) b a
@

and corresponding @KnownNat2@ instance:

@
instance (KnownNat a, KnownNat b) => KnownNat2 \"TestFunctions.Max\" a b where
  type KnownNatF2 \"TestFunctions.Max\" = MaxSym2
  natSing2 = let x = natVal (Proxy @ a)
                 y = natVal (Proxy @ b)
                 z = max x y
             in  SNatKn z
  \{\-# INLINE natSing2 \#-\}
@

the plugin can derive a @KnownNat (Max x y + 1)@ constraint given only a
@KnownNat x@ and @KnownNat y@ constraint:

@
h :: forall x y . (KnownNat x, KnownNat y) => Proxy x -> Proxy y -> Integer
h _ _ = natVal (Proxy :: Proxy (Max x y + 1))
@

To use the plugin, add the

@
OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver
@

Pragma to the header of your file.

-}
plugin :: Plugin
plugin = defaultPlugin { tcPlugin = const $ Just normalisePlugin }

normalisePlugin :: TcPlugin
normalisePlugin = tracePlugin "ghc-typelits-knownnat"
  TcPlugin { tcPluginInit  = lookupKnownNatDefs
           , tcPluginSolve = solveKnownNat
           , tcPluginStop  = const (return ())
           }

solveKnownNat :: KnownNatDefs -> [Ct] -> [Ct] -> [Ct]
              -> TcPluginM TcPluginResult
solveKnownNat _defs _givens _deriveds []      = return (TcPluginOk [] [])
solveKnownNat defs  givens  _deriveds wanteds = do
  -- GHC 7.10 puts deriveds with the wanteds, so filter them out
  let wanteds'   = filter (isWanted . ctEvidence) wanteds
      kn_wanteds = mapMaybe toKnConstraint wanteds'
  case kn_wanteds of
    [] -> return (TcPluginOk [] [])
    _  -> do
      -- Make a lookup table for all the [G]iven constraints
      given_map <- mapM (fmap toGivenEntry . zonkCt) givens
      -- Try to solve the wanted KnownNat constraints given the [G]iven
      -- KnownNat constraints
      (solved,new) <- (unzip . catMaybes) <$> (mapM (constraintToEvTerm defs given_map) kn_wanteds)
      return (TcPluginOk solved (concat new))

-- | Get the KnownNat constraints
toKnConstraint :: Ct -> Maybe KnConstraint
toKnConstraint ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
  ClassPred cls [ty]
    |  className cls == knownNatClassName
    -> Just (ct,cls,ty)
  _ -> Nothing

-- | Create a look-up entry for a [G]iven constraint.
toGivenEntry :: Ct -> (CType,EvTerm)
toGivenEntry ct = let ct_ev = ctEvidence ct
                      c_ty  = ctEvPred   ct_ev
                      ev    = ctEvTerm   ct_ev
                  in  (CType c_ty,ev)

-- | Normalise a type to Sum-of-Product type form as defined in the
-- `ghc-typelits-natnormalise` package.
normaliseSOP :: Type -> Type
normaliseSOP = reifySOP . normaliseNat

-- | Find the \"magic\" classes and instances in "GHC.TypeLits.KnownNat"
lookupKnownNatDefs :: TcPluginM KnownNatDefs
lookupKnownNatDefs = do
    md     <- lookupModule myModule myPackage
    kn2C   <- look md "KnownNat2"
    kn3C   <- look md "KnownNat3"
    return $ (\case { 2 -> Just kn2C
                    ; 3 -> Just kn3C
                    ; _ -> Nothing
                    })
  where
    look md s = do
      nm   <- lookupName md (mkTcOcc s)
      tcLookupClass nm

    myModule  = mkModuleName "GHC.TypeLits.KnownNat"
    myPackage = fsLit "ghc-typelits-knownnat"

-- | Try to create evidence for a wanted constraint
constraintToEvTerm :: KnownNatDefs     -- ^ The "magic" KnownNatN classes
                   -> [(CType,EvTerm)] -- All the [G]iven constraints
                   -> KnConstraint
                   -> TcPluginM (Maybe ((EvTerm,Ct),[Ct]))
constraintToEvTerm defs givens (ct,cls,op) = do
    -- 1. Normalise to SOP normal form
    let ty = normaliseSOP op
    -- 2. Determine if we are an offset apart from a [G]iven constraint
    offsetM <- offset ty
    evM     <- case offsetM of
                 -- 3.a If so, we are done
                 found@Just {} -> return found
                 -- 3.b If not, we check if the outer type-level operation
                 -- has a corresponding KnownNat<N> instance.
                 _ -> go ty
    return (first (,ct) <$> evM)
  where
    -- Determine whether the outer type-level operation has a corresponding
    -- KnownNat<N> instance, where /N/ corresponds to the arity of the
    -- type-level operation
    go :: Type -> TcPluginM (Maybe (EvTerm,[Ct]))
    go (go_other -> Just ev) = return (Just (ev,[]))
    go ty@(TyConApp tc args)
      | let tcNm = tyConName tc
      , Just m <- nameModule_maybe tcNm
      , Just knN_cls <- defs (length args)
      = do let mS    = moduleNameString (moduleName m)
               tcS   = occNameString (nameOccName tcNm)
               fn    = mkStrLitTy (fsLit (mS ++ "." ++ tcS))
               args' = fn:args
           ienv <- getInstEnvs
           case lookupUniqueInstEnv ienv knN_cls args' of
             Right (inst, _) -> do
               let df_id   = instanceDFunId inst
                   df      = (knN_cls,df_id)
                   df_args = fst                  -- [KnownNat x, KnownNat y]
                           . splitFunTys          -- ([KnownNat x, KnowNat y], DKnownNat2 "+" x y)
                           . (`piResultTys` args) -- (KnowNat x, KnownNat y) => DKnownNat2 "+" x y
                           $ idType df_id         -- forall a b . (KnownNat a, KnownNat b) => DKnownNat2 "+" a b
               (evs,new) <- unzip <$> mapM go_arg df_args
               return ((,concat new) <$> makeOpDict df cls args' op evs)
             _ -> return ((,[]) <$> go_other ty)
    go _ = return Nothing

    -- Get EvTerm arguments for type-level operations. If they do not exist
    -- as [G]iven constraints, then generate new [W]anted constraints
    go_arg :: PredType -> TcPluginM (EvTerm,[Ct])
    go_arg ty = case lookup (CType ty) givens of
      Just ev -> return (ev,[])
      _ -> do
        wanted <- newWanted (ctLoc ct) ty
        let ev = ctEvTerm wanted
        return (ev,[mkNonCanonical wanted])

    -- Fall through case: look up the normalised [W]anted constraint in the list
    -- of [G]iven constraints.
    go_other :: Type -> Maybe EvTerm
    go_other ty =
      let knClsTc = classTyCon cls
          kn      = mkTyConApp knClsTc [ty]
          cast    = if CType ty == CType op
                       then Just
                       else makeKnCoercion cls ty op
      in  cast =<< lookup (CType kn) givens

    -- Find a known constraint for a wanted, so that (modulo normalization)
    -- the two are a constant offset apart.
    offset :: Type -> TcPluginM (Maybe (EvTerm,[Ct]))
    offset want = runMaybeT $ do
      let unKn ty' = case classifyPredType ty' of
                       ClassPred cls' [ty'']
                         | className cls' == knownNatClassName
                         -> Just ty''
                       _ -> Nothing
          -- Get only the [G]iven KnownNat constraints
          knowns   = mapMaybe (unKn . unCType . fst) givens
          -- pair up the sum-of-products KnownNat constraints
          -- with the original Nat operation
          subWant  = mkTyConApp typeNatSubTyCon . (:[want])
          exploded = map (normaliseNat . subWant &&& id) knowns
          -- interesting cases for us are those where
          -- wanted and given only differ by a constant
          examine (diff,entire) =
            case diff of
              S [P [I n]] -> Just (entire, n)
              _ -> Nothing
          interesting = mapMaybe examine exploded
      -- convert the first suitable evidence
      ((h,corr):_) <- pure interesting
      let x = case corr of
                0 -> h
                _ | corr < 0  -> mkTyConApp typeNatAddTyCon [h,mkNumLitTy (negate corr)]
                  | otherwise -> mkTyConApp typeNatSubTyCon [h,mkNumLitTy corr]
      MaybeT (go x)

{- |
Given:

* A "magic" class, and corresponding instance dictionary function, for a
  type-level arithmetic operation
* Two KnownNat dictionaries

makeOpDict instantiates the dictionary function with the KnownNat dictionaries,
and coerces it to a KnownNat dictionary. i.e. for KnownNat2, the "magic"
dictionary for binary functions, the coercion happens in the following steps:

1. KnownNat2 "+" a b           -> SNatKn (KnownNatF2 "+" a b)
2. SNatKn (KnownNatF2 "+" a b) -> Integer
3. Integer                     -> SNat (a + b)
4. SNat (a + b)                -> KnownNat (a + b)

this process is mirrored for the dictionary functions of a higher arity
-}
makeOpDict :: (Class,DFunId) -- ^ "magic" class function and dictionary function id
           -> Class          -- ^ KnownNat class
           -> [Type]         -- ^ Argument types
           -> Type           -- ^ Type of the result
           -> [EvTerm]       -- ^ Evidence arguments
           -> Maybe EvTerm
makeOpDict (opCls,dfid) knCls tyArgs z evArgs
  | Just (_, kn_co_dict) <- tcInstNewTyCon_maybe (classTyCon knCls) [z]
    -- KnownNat n ~ SNat n
  , [ kn_meth ] <- classMethods knCls
  , Just kn_tcRep <- tyConAppTyCon_maybe -- SNat
                      $ funResultTy      -- SNat n
                      $ dropForAlls      -- KnownNat n => SNat n
                      $ idType kn_meth   -- forall n. KnownNat n => SNat n
  , Just (_, kn_co_rep) <- tcInstNewTyCon_maybe kn_tcRep [z]
    -- SNat n ~ Integer
  , Just (_, op_co_dict) <- tcInstNewTyCon_maybe (classTyCon opCls) tyArgs
    -- KnownNatAdd a b ~ SNatKn (a+b)
  , [ op_meth ] <- classMethods opCls
  , Just (op_tcRep,op_args) <- splitTyConApp_maybe        -- (SNatKn, [KnownNatF2 f x y])
                                 $ funResultTy            -- SNatKn (KnownNatF2 f x y)
                                 $ (`piResultTys` tyArgs) -- KnownNatAdd f x y => SNatKn (KnownNatF2 f x y)
                                 $ idType op_meth         -- forall f a b . KnownNat2 f a b => SNatKn (KnownNatF2 f a b)
  , Just (_, op_co_rep) <- tcInstNewTyCon_maybe op_tcRep op_args
    -- SNatKn (a+b) ~ Integer
  , let dfun_inst = EvDFunApp dfid (tail tyArgs) evArgs
        -- KnownNatAdd a b
        op_to_kn  = mkTcTransCo (mkTcTransCo op_co_dict op_co_rep)
                                (mkTcSymCo (mkTcTransCo kn_co_dict kn_co_rep))
        -- KnownNatAdd a b ~ KnownNat (a+b)
        ev_tm     = mkEvCast dfun_inst op_to_kn
  = Just ev_tm
  | otherwise
  = Nothing

{-
Given:
* A KnownNat dictionary evidence over a type x
* a desired type z
makeKnCoercion assembles a coercion from a KnownNat x
dictionary to a KnownNat z dictionary and applies it
to the passed-in evidence.
The coercion happens in the following steps:
1. KnownNat x -> SNat x
2. SNat x     -> Integer
3. Integer    -> SNat z
4. SNat z     -> KnownNat z
-}
makeKnCoercion :: Class          -- ^ KnownNat class
               -> Type           -- ^ Type of the argument
               -> Type           -- ^ Type of the result
               -> EvTerm         -- ^ KnownNat dictionary for the argument
               -> Maybe EvTerm
makeKnCoercion knCls x z xEv
  | Just (_, kn_co_dict_z) <- tcInstNewTyCon_maybe (classTyCon knCls) [z]
    -- KnownNat z ~ SNat z
  , [ kn_meth ] <- classMethods knCls
  , Just kn_tcRep <- tyConAppTyCon_maybe -- SNat
                      $ funResultTy      -- SNat n
                      $ dropForAlls      -- KnownNat n => SNat n
                      $ idType kn_meth   -- forall n. KnownNat n => SNat n
  , Just (_, kn_co_rep_z) <- tcInstNewTyCon_maybe kn_tcRep [z]
    -- SNat z ~ Integer
  , Just (_, kn_co_rep_x) <- tcInstNewTyCon_maybe kn_tcRep [x]
    -- Integer ~ SNat x
  , Just (_, kn_co_dict_x) <- tcInstNewTyCon_maybe (classTyCon knCls) [x]
    -- SNat x ~ KnownNat x
  = Just . mkEvCast xEv $ (kn_co_dict_x `mkTcTransCo` kn_co_rep_x) `mkTcTransCo` mkTcSymCo (kn_co_dict_z `mkTcTransCo` kn_co_rep_z)
  | otherwise = Nothing
