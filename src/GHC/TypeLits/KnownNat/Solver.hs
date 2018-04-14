{-|
Copyright  :  (C) 2016     , University of Twente,
                  2017-2018, QBayLogic B.V.,
                  2017     , Google Inc.
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

{-# LANGUAGE CPP           #-}
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
#if MIN_VERSION_ghc(8,4,0)
import GHC.TcPluginM.Extra          (flattenGivens, mkSubst', substType)
#endif
import GHC.TypeLits.Normalise.SOP   (SOP (..), Product (..), Symbol (..))
import GHC.TypeLits.Normalise.Unify (CType (..),normaliseNat,reifySOP)

-- GHC API
import Class      (Class, classMethods, className, classTyCon)
import FamInst    (tcInstNewTyCon_maybe)
import FastString (fsLit)
import Id         (idType)
import InstEnv    (instanceDFunId,lookupUniqueInstEnv)
#if MIN_VERSION_ghc(8,5,0)
import MkCore     (mkNaturalExpr)
#endif
import Module     (mkModuleName, moduleName, moduleNameString)
import Name       (nameModule_maybe, nameOccName)
import OccName    (mkTcOcc, occNameString)
import Plugins    (Plugin (..), defaultPlugin)
import PrelNames  (knownNatClassName)
#if MIN_VERSION_ghc(8,5,0)
import TcEvidence (EvTerm (..), EvExpr, evDFunApp, mkEvCast, mkTcSymCo, mkTcTransCo)
#else
import TcEvidence (EvTerm (..), EvLit (EvNum), mkEvCast, mkTcSymCo, mkTcTransCo)
#endif
#if MIN_VERSION_ghc(8,5,0)
import TcPluginM  (unsafeTcPluginTcM)
#endif
#if !MIN_VERSION_ghc(8,4,0)
import TcPluginM  (zonkCt)
#endif
import TcPluginM  (TcPluginM, tcLookupClass, getInstEnvs)
import TcRnTypes  (Ct, TcPlugin(..), TcPluginResult (..), ctEvidence, ctEvLoc,
#if MIN_VERSION_ghc(8,5,0)
                   ctEvPred, ctEvExpr, ctLoc, ctLocSpan, isWanted,
#else
                   ctEvPred, ctEvTerm, ctLoc, ctLocSpan, isWanted,
#endif
                   mkNonCanonical, setCtLoc, setCtLocSpan)
import TcTypeNats (typeNatAddTyCon, typeNatSubTyCon)
import Type
  (EqRel (NomEq), PredTree (ClassPred,EqPred), PredType, classifyPredType,
   dropForAlls, eqType, funResultTy, mkNumLitTy, mkStrLitTy, mkTyConApp,
   piResultTys, splitFunTys, splitTyConApp_maybe, tyConAppTyCon_maybe)
import TyCon      (tyConName)
import TyCoRep    (Type (..), TyLit (..))
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

$(genDefunSymbols [''Max]) -- creates the 'MaxSym0' symbol
@

and corresponding @KnownNat2@ instance:

@
instance (KnownNat a, KnownNat b) => KnownNat2 \"TestFunctions.Max\" a b where
  type KnownNatF2 \"TestFunctions.Max\" = MaxSym0
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
#if MIN_VERSION_ghc(8,4,0)
      subst      = mkSubst' givens
      kn_wanteds = map (\(x,y,z) -> (x,y,substType subst z))
                 $ mapMaybe toKnConstraint wanteds'
#else
      kn_wanteds = mapMaybe toKnConstraint wanteds'
#endif
  case kn_wanteds of
    [] -> return (TcPluginOk [] [])
    _  -> do
      -- Make a lookup table for all the [G]iven constraints
#if MIN_VERSION_ghc(8,4,0)
      let given_map = map toGivenEntry (givens ++ flattenGivens givens)
#else
      given_map <- mapM (fmap toGivenEntry . zonkCt) givens
#endif
      -- Try to solve the wanted KnownNat constraints given the [G]iven
      -- KnownNat constraints
      (solved,new) <- (unzip . catMaybes) <$> (mapM (constraintToEvTerm defs given_map) kn_wanteds)
#if MIN_VERSION_ghc(8,5,0)
      return (TcPluginOk (map (first EvExpr) solved) (concat new))
#else
      return (TcPluginOk solved (concat new))
#endif

-- | Get the KnownNat constraints
toKnConstraint :: Ct -> Maybe KnConstraint
toKnConstraint ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
  ClassPred cls [ty]
    |  className cls == knownNatClassName
    -> Just (ct,cls,ty)
  _ -> Nothing

-- | Create a look-up entry for a [G]iven constraint.
#if MIN_VERSION_ghc(8,5,0)
toGivenEntry :: Ct -> (CType,EvExpr)
#else
toGivenEntry :: Ct -> (CType,EvTerm)
#endif
toGivenEntry ct = let ct_ev = ctEvidence ct
                      c_ty  = ctEvPred   ct_ev
#if MIN_VERSION_ghc(8,5,0)
                      ev    = ctEvExpr   ct_ev
#else
                      ev    = ctEvTerm   ct_ev
#endif
                  in  (CType c_ty,ev)

-- | Normalise a type to Sum-of-Product type form as defined in the
-- `ghc-typelits-natnormalise` package.
normaliseSOP :: Type -> Type
normaliseSOP = reifySOP . normaliseNat

-- | Find the \"magic\" classes and instances in "GHC.TypeLits.KnownNat"
lookupKnownNatDefs :: TcPluginM KnownNatDefs
lookupKnownNatDefs = do
    md     <- lookupModule myModule myPackage
    kn1C   <- look md "KnownNat1"
    kn2C   <- look md "KnownNat2"
    kn3C   <- look md "KnownNat3"
    return $ (\case { 1 -> Just kn1C
                    ; 2 -> Just kn2C
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
constraintToEvTerm
  :: KnownNatDefs     -- ^ The "magic" KnownNatN classes
#if MIN_VERSION_ghc(8,5,0)
  -> [(CType,EvExpr)]
  -- All the [G]iven constraints
#else
  -> [(CType,EvTerm)]
  -- All the [G]iven constraints
#endif
  -> KnConstraint
#if MIN_VERSION_ghc(8,5,0)
  -> TcPluginM (Maybe ((EvExpr,Ct),[Ct]))
#else
  -> TcPluginM (Maybe ((EvTerm,Ct),[Ct]))
#endif
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
#if MIN_VERSION_ghc(8,5,0)
    go :: Type -> TcPluginM (Maybe (EvExpr,[Ct]))
#else
    go :: Type -> TcPluginM (Maybe (EvTerm,[Ct]))
#endif
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
    go (LitTy (NumTyLit i))
      -- Let GHC solve simple Literal constraints
      | LitTy _ <- op
      = return Nothing
      -- This plugin only solves Literal KnownNat's that needed to be normalised
      -- first
      | otherwise
#if MIN_VERSION_ghc(8,5,0)
      = (fmap (,[])) <$> makeLitDict cls op i
#else
      = return ((,[]) <$> makeLitDict cls op i)
#endif
    go _ = return Nothing

    -- Get EvTerm arguments for type-level operations. If they do not exist
    -- as [G]iven constraints, then generate new [W]anted constraints
#if MIN_VERSION_ghc(8,5,0)
    go_arg :: PredType -> TcPluginM (EvExpr,[Ct])
#else
    go_arg :: PredType -> TcPluginM (EvTerm,[Ct])
#endif
    go_arg ty = case lookup (CType ty) givens of
      Just ev -> return (ev,[])
      _ -> do
        -- Create a new wanted constraint
        wantedCtEv <- newWanted (ctLoc ct) ty
#if MIN_VERSION_ghc(8,5,0)
        let ev      = ctEvExpr wantedCtEv
#else
        let ev      = ctEvTerm wantedCtEv
#endif
            wanted  = mkNonCanonical wantedCtEv
        -- Set the source-location of the new wanted constraint to the source
        -- location of the [W]anted constraint we are currently trying to solve
        let ct_ls   = ctLocSpan (ctLoc ct)
            ctl     = ctEvLoc  wantedCtEv
            wanted' = setCtLoc wanted (setCtLocSpan ctl ct_ls)
        return (ev,[wanted'])

    -- Fall through case: look up the normalised [W]anted constraint in the list
    -- of [G]iven constraints.
#if MIN_VERSION_ghc(8,5,0)
    go_other :: Type -> Maybe EvExpr
#else
    go_other :: Type -> Maybe EvTerm
#endif
    go_other ty =
      let knClsTc = classTyCon cls
          kn      = mkTyConApp knClsTc [ty]
          cast    = if CType ty == CType op
                       then Just
                       else makeKnCoercion cls ty op
      in  cast =<< lookup (CType kn) givens

    -- Find a known constraint for a wanted, so that (modulo normalization)
    -- the two are a constant offset apart.
#if MIN_VERSION_ghc(8,5,0)
    offset :: Type -> TcPluginM (Maybe (EvExpr,[Ct]))
#else
    offset :: Type -> TcPluginM (Maybe (EvTerm,[Ct]))
#endif
    offset want = runMaybeT $ do
      let -- Get the knownnat contraints
          unKn ty' = case classifyPredType ty' of
                       ClassPred cls' [ty'']
                         | className cls' == knownNatClassName
                         -> Just ty''
                       _ -> Nothing
          -- Get the rewrites
          unEq ty' = case classifyPredType ty' of
                       EqPred NomEq ty1 ty2 -> Just (ty1,ty2)
                       _ -> Nothing
          rewrites = mapMaybe (unEq . unCType . fst) givens
          -- Rewrite
          rewriteTy tyK (ty1,ty2) | ty1 `eqType` tyK = Just ty2
                                  | ty2 `eqType` tyK = Just ty1
                                  | otherwise        = Nothing
          -- Get only the [G]iven KnownNat constraints
          knowns   = mapMaybe (unKn . unCType . fst) givens
          -- Get all the rewritten KNs
          knownsR  = catMaybes $ concatMap (\t -> map (rewriteTy t) rewrites) knowns
          -- pair up the sum-of-products KnownNat constraints
          -- with the original Nat operation
          subWant  = mkTyConApp typeNatSubTyCon . (:[want])
          exploded = map (normaliseNat . subWant &&& id) (knowns ++ knownsR)
          -- interesting cases for us are those where
          -- wanted and given only differ by a constant
          examineDiff (S [P [I n]]) entire = Just (entire,I n)
          examineDiff (S [P [V v]]) entire = Just (entire,V v)
          examineDiff _ _ = Nothing
          interesting = mapMaybe (uncurry examineDiff) exploded
      -- convert the first suitable evidence
      ((h,corr):_) <- pure interesting
      let x = case corr of
                I 0 -> h
                I i | i < 0     -> mkTyConApp typeNatAddTyCon [h,mkNumLitTy (negate i)]
                    | otherwise -> mkTyConApp typeNatSubTyCon [h,mkNumLitTy i]
                _ -> mkTyConApp typeNatSubTyCon [h,reifySOP (S [P [corr]])]
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
#if MIN_VERSION_ghc(8,5,0)
           -> [EvExpr]
           -- ^ Evidence arguments
           -> Maybe EvExpr
#else
           -> [EvTerm]
           -- ^ Evidence arguments
           -> Maybe EvTerm
#endif
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
#if MIN_VERSION_ghc(8,5,0)
  , let dfun_inst = evDFunApp dfid (tail tyArgs) evArgs
#else
  , let dfun_inst = EvDFunApp dfid (tail tyArgs) evArgs
#endif
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
#if MIN_VERSION_ghc(8,5,0)
               -> EvExpr
               -- ^ KnownNat dictionary for the argument
               -> Maybe EvExpr
#else
               -> EvTerm
               -- ^ KnownNat dictionary for the argument
               -> Maybe EvTerm
#endif
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

-- | THIS CODE IS COPIED FROM:
-- https://github.com/ghc/ghc/blob/8035d1a5dc7290e8d3d61446ee4861e0b460214e/compiler/typecheck/TcInteract.hs#L1973
--
-- makeLitDict adds a coercion that will convert the literal into a dictionary
-- of the appropriate type.  See Note [KnownNat & KnownSymbol and EvLit]
-- in TcEvidence.  The coercion happens in 2 steps:
--
--     Integer -> SNat n     -- representation of literal to singleton
--     SNat n  -> KnownNat n -- singleton to dictionary
#if MIN_VERSION_ghc(8,5,0)
makeLitDict :: Class -> Type -> Integer -> TcPluginM (Maybe EvExpr)
#else
makeLitDict :: Class -> Type -> Integer -> Maybe EvTerm
#endif
makeLitDict clas ty i
  | Just (_, co_dict) <- tcInstNewTyCon_maybe (classTyCon clas) [ty]
    -- co_dict :: KnownNat n ~ SNat n
  , [ meth ]   <- classMethods clas
  , Just tcRep <- tyConAppTyCon_maybe -- SNat
                    $ funResultTy     -- SNat n
                    $ dropForAlls     -- KnownNat n => SNat n
                    $ idType meth     -- forall n. KnownNat n => SNat n
  , Just (_, co_rep) <- tcInstNewTyCon_maybe tcRep [ty]
        -- SNat n ~ Integer
#if MIN_VERSION_ghc(8,5,0)
  = do
    et <- unsafeTcPluginTcM (mkNaturalExpr i)
    let ev_tm = mkEvCast et (mkTcSymCo (mkTcTransCo co_dict co_rep))
    return (Just ev_tm)
  | otherwise
  = return Nothing
#else
  , let ev_tm = mkEvCast (EvLit (EvNum i)) (mkTcSymCo (mkTcTransCo co_dict co_rep))
  = Just ev_tm
  | otherwise
  = Nothing
#endif
