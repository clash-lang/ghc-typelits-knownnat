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
  natSing2 = let x = natVal (Proxy @a)
                 y = natVal (Proxy @b)
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
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns  #-}

{-# LANGUAGE Trustworthy   #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module GHC.TypeLits.KnownNat.Solver
  ( plugin )
where

-- external
import Control.Arrow                ((&&&), first)
import Control.Monad.Trans.Maybe    (MaybeT (..))
import Control.Monad.Trans.Writer.Strict
import Data.Maybe                   (catMaybes,mapMaybe)
#if MIN_VERSION_ghc(8,4,0)
import GHC.TcPluginM.Extra          (flattenGivens, mkSubst', substType)
#endif
import GHC.TypeLits.Normalise.SOP   (SOP (..), Product (..), Symbol (..))
import GHC.TypeLits.Normalise.Unify (CType (..),normaliseNat,reifySOP)

-- GHC API
#if MIN_VERSION_ghc(9,0,0)
import GHC.Builtin.Names (knownNatClassName)
import GHC.Builtin.Types (boolTy)
import GHC.Builtin.Types.Literals (typeNatAddTyCon, typeNatDivTyCon, typeNatSubTyCon)
#if MIN_VERSION_ghc(9,2,0)
import GHC.Builtin.Types (promotedFalseDataCon, promotedTrueDataCon)
import GHC.Builtin.Types.Literals (typeNatCmpTyCon)
#endif
import GHC.Core.Class (classMethods)
import GHC.Core.InstEnv (instanceDFunId, lookupUniqueInstEnv)
import GHC.Core.Make (mkNaturalExpr)
import GHC.Core.TyCo.Rep (Type (..), TyLit (..), UnivCoProvenance (PluginProv))
import GHC.Core.Type
  (dropForAlls, funResultTy,
   piResultTys, splitFunTys,
   irrelevantMult)
import GHC.Driver.Plugins (Plugin (..), defaultPlugin, purePlugin)
import GHC.Tc.Instance.Family (tcInstNewTyCon_maybe)
import GHC.Tc.Types.Constraint
  (ctLocSpan, 
   setCtLoc, setCtLocSpan)
import GHC.Tc.Types.Evidence
  (mkEvCast, mkTcSymCo, mkTcTransCo)
import GHC.Types.Id (idType)
import GHC.Types.Name (nameModule_maybe, nameOccName)
import GHC.Types.Name.Occurrence (occNameString)
import GHC.Types.Var (DFunId)
import GHC.Unit.Module (moduleName, moduleNameString)
#else
import Class      (Class, classMethods, className, classTyCon)
#if MIN_VERSION_ghc(8,6,0)
import Coercion   (Role (Representational), mkUnivCo)
#endif
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
#if MIN_VERSION_ghc(8,6,0)
import Plugins    (purePlugin)
#endif
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
import TcRnTypes  (TcPlugin(..), TcPluginResult (..))
import TcTypeNats (typeNatAddTyCon, typeNatSubTyCon)
#if MIN_VERSION_ghc(8,4,0)
import TcTypeNats (typeNatDivTyCon)
#endif
import Type
  (PredType,
   dropForAlls, eqType, funResultTy, mkNumLitTy, mkStrLitTy, mkTyConApp,
   piResultTys, splitFunTys, splitTyConApp_maybe, tyConAppTyCon_maybe, typeKind)
import TyCon      (tyConName)
import TyCoRep    (Type (..), TyLit (..))
#if MIN_VERSION_ghc(8,6,0)
import TyCoRep    (UnivCoProvenance (PluginProv))
import TysWiredIn (boolTy)
#endif
import Var        (DFunId)

#if MIN_VERSION_ghc(8,10,0)
import Constraint
  (Ct, ctEvExpr, ctEvidence, ctEvLoc, ctEvPred, ctLoc, ctLocSpan, isWanted,
   mkNonCanonical, setCtLoc, setCtLocSpan)
import Predicate (EqRel (NomEq), Pred (ClassPred,EqPred), classifyPredType)
#else
import TcRnTypes
  (Ct, ctEvidence, ctEvLoc, ctEvPred, ctLoc, ctLocSpan, isWanted, mkNonCanonical,
   setCtLoc, setCtLocSpan)
import Type      (EqRel (NomEq), PredTree (ClassPred,EqPred), classifyPredType)
#if MIN_VERSION_ghc(8,5,0)
import TcRnTypes (ctEvExpr)
#else
import TcRnTypes (ctEvTerm)
#endif
#endif
#endif
import GHC.TcPlugin.API
import GHC.TypeLits.KnownNat

-- | Classes and instances from "GHC.TypeLits.KnownNat"
data KnownNatDefs
  = KnownNatDefs
  { knownBool     :: Class
  , knownBoolNat2 :: Class
  , knownNat2Bool :: Class
  , knownNatN     :: Int -> Maybe Class -- ^ KnownNat{N}
  }

-- | Simple newtype wrapper to distinguish the original (flattened) argument of
-- knownnat from the un-flattened version that we work with internally.
newtype Orig a = Orig { unOrig :: a }

-- | KnownNat constraints
type KnConstraint = (Ct    -- The constraint
                    ,Class -- KnownNat class
                    ,Type  -- The argument to KnownNat
                    ,Orig Type  -- Original, flattened, argument to KnownNat
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
plugin
  = defaultPlugin
  { tcPlugin = const $ Just $ mkTcPlugin normalisePlugin
#if MIN_VERSION_ghc(8,6,0)
  , pluginRecompile = purePlugin
#endif
  }

normalisePlugin :: TcPlugin
normalisePlugin =
  TcPlugin { tcPluginInit  = lookupKnownNatDefs
           , tcPluginSolve = solveKnownNat
           , tcPluginRewrite = const emptyUFM
           , tcPluginStop  = const (return ())
           }

solveKnownNat :: KnownNatDefs -> [Ct] -> [Ct]
              -> TcPluginM 'Solve TcPluginSolveResult
solveKnownNat _defs _givens []      = return (TcPluginOk [] [])
solveKnownNat defs  givens  wanteds = do
  -- GHC 7.10 puts deriveds with the wanteds, so filter them out
  let wanteds'   = filter (isWanted . ctEvidence) wanteds
#if MIN_VERSION_ghc(8,4,0)
      subst      = map fst
                 $ mkSubst' givens
      kn_wanteds = map (\(x,y,z,orig) -> (x,y,substType subst z,orig))
                 $ mapMaybe (toKnConstraint defs) wanteds'
#else
      kn_wanteds = mapMaybe (toKnConstraint defs) wanteds'
#endif
  case kn_wanteds of
    [] -> return (TcPluginOk [] [])
    _  -> do
      -- Make a lookup table for all the [G]iven constraints
#if MIN_VERSION_ghc(8,4,0)
      let given_map = map toGivenEntry (flattenGivens givens)
#else
      given_map <- mapM (fmap toGivenEntry . zonkCt) givens
#endif
      -- Try to solve the wanted KnownNat constraints given the [G]iven
      -- KnownNat constraints
      (solved,new) <- (unzip . catMaybes) <$> (mapM (constraintToEvTerm defs given_map) kn_wanteds)
      return (TcPluginOk solved (concat new))

-- | Get the KnownNat constraints
toKnConstraint :: KnownNatDefs -> Ct -> Maybe KnConstraint
toKnConstraint defs ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
  ClassPred cls [ty]
    |  className cls == knownNatClassName ||
       className cls == className (knownBool defs)
    -> Just (ct,cls,ty,Orig ty)
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

-- | Find the \"magic\" classes and instances in "GHC.TypeLits.KnownNat"
lookupKnownNatDefs :: TcPluginM 'Init KnownNatDefs
lookupKnownNatDefs = do
    kbC <- lookupTHName ''KnownBool >>= tcLookupClass
    kbn2C  <- lookupTHName ''KnownBoolNat2 >>= tcLookupClass
    kn2bC  <- lookupTHName ''KnownNat2Bool >>= tcLookupClass
    kn1C   <- lookupTHName ''KnownNat1 >>= tcLookupClass
    kn2C   <- lookupTHName ''KnownNat2 >>= tcLookupClass
    kn3C   <- lookupTHName ''KnownNat3 >>= tcLookupClass
    return KnownNatDefs
           { knownBool     = kbC
           , knownBoolNat2 = kbn2C
           , knownNat2Bool = kn2bC
           , knownNatN     = \case { 1 -> Just kn1C
                                   ; 2 -> Just kn2C
                                   ; 3 -> Just kn3C
                                   ; _ -> Nothing
                                   }
           }

-- | Try to create evidence for a wanted constraint
constraintToEvTerm
  :: KnownNatDefs     -- ^ The "magic" KnownNatN classes
#if MIN_VERSION_ghc(8,5,0)
  -> [(CType,EvExpr)]
#else
  -> [(CType,EvTerm)]
#endif
  -- All the [G]iven constraints

  -> KnConstraint
  -> TcPluginM 'Solve (Maybe ((EvTerm,Ct),[Ct]))
constraintToEvTerm defs givens (ct,cls,op,orig) = do
    -- 1. Determine if we are an offset apart from a [G]iven constraint
    offsetM <- offset op
    evM     <- case offsetM of
                 -- 3.a If so, we are done
                 found@Just {} -> return found
                 -- 3.b If not, we check if the outer type-level operation
                 -- has a corresponding KnownNat<N> instance.
                 _ -> go op
    return ((first (,ct)) <$> evM)
  where
    -- Determine whether the outer type-level operation has a corresponding
    -- KnownNat<N> instance, where /N/ corresponds to the arity of the
    -- type-level operation
    go :: Type -> TcPluginM 'Solve (Maybe (EvTerm,[Ct]))
    go (go_other -> Just ev) = return (Just (ev,[]))
    go ty@(TyConApp tc args0)
      | let tcNm = tyConName tc
      , Just m <- nameModule_maybe tcNm
      = do
        ienv <- getInstEnvs
        let mS  = moduleNameString (moduleName m)
            tcS = occNameString (nameOccName tcNm)
            fn0 = mS ++ "." ++ tcS
            fn1 = mkStrLitTy (fsLit fn0)
            args1 = fn1:args0
            instM = case () of
              () | Just knN_cls    <- knownNatN defs (length args0)
                 , Right (inst, _) <- lookupUniqueInstEnv ienv knN_cls args1
                 -> Just (inst,knN_cls,args0,args1)
#if MIN_VERSION_base(4,16,0)
                 | fn0 == "Data.Type.Ord.OrdCond"
                 , [_,cmpNat,TyConApp t1 [],TyConApp t2 [],TyConApp f1 []] <- args0
                 , TyConApp cmpNatTc args2 <- cmpNat
                 , cmpNatTc == typeNatCmpTyCon
                 , t1 == promotedTrueDataCon
                 , t2 == promotedTrueDataCon
                 , f1 == promotedFalseDataCon
                 , let knN_cls = knownBoolNat2 defs
                       ki      = typeKind (head args2)
                       args1N  = ki:fn1:args2
                 , Right (inst,_) <- lookupUniqueInstEnv ienv knN_cls args1N
                 -> Just (inst,knN_cls,args2,args1N)
#endif
                 | length args0 == 2
                 , let knN_cls = knownBoolNat2 defs
                       ki      = typeKind (head args0)
                       args1N  = ki:args1
                 , Right (inst, _) <- lookupUniqueInstEnv ienv knN_cls args1N
                 -> Just (inst,knN_cls,args0,args1N)
                 | length args0 == 4
                 , fn0 == "Data.Type.Bool.If"
                 , let args0N = tail args0
                       args1N = head args0:fn1:tail args0
                       knN_cls = knownNat2Bool defs
                 , Right (inst, _) <- lookupUniqueInstEnv ienv knN_cls args1N
                 -> Just (inst,knN_cls,args0N,args1N)
                 | otherwise
                 -> Nothing
        case instM of
          Just (inst,knN_cls,args0N,args1N) -> do
            let df_id   = instanceDFunId inst
                df      = (knN_cls,df_id)
                df_args = fst                  -- [KnownNat x, KnownNat y]
                        . splitFunTys          -- ([KnownNat x, KnowNat y], DKnownNat2 "+" x y)
                        . (`piResultTys` args0N) -- (KnowNat x, KnownNat y) => DKnownNat2 "+" x y
                        $ idType df_id         -- forall a b . (KnownNat a, KnownNat b) => DKnownNat2 "+" a b
#if MIN_VERSION_ghc(9,0,0)
            (evs,new) <- unzip <$> mapM (go_arg . irrelevantMult) df_args
#else
            (evs,new) <- unzip <$> mapM go_arg df_args
#endif
            if className cls == className (knownBool defs)
               -- Create evidence using the original, flattened, argument of
               -- the KnownNat we're trying to solve. Not doing this results in
               -- GHC panics for:
               -- https://gist.github.com/christiaanb/0d204fe19f89b28f1f8d24feb63f1e63
               --
               -- That's because the flattened KnownNat we're asked to solve is
               -- [W] KnownNat fsk
               -- given:
               -- [G] fsk ~ CLog 2 n + 1
               -- [G] fsk2 ~ n
               -- [G] fsk2 ~ n + m
               --
               -- Our flattening picks one of the solution, so we try to solve
               -- [W] KnownNat (CLog 2 n + 1)
               --
               -- Turns out, GHC wanted us to solve:
               -- [W] KnownNat (CLog 2 (n + m) + 1)
               --
               -- But we have no way of knowing this! Solving the "wrong" expansion
               -- of 'fsk' results in:
               --
               -- ghc: panic! (the 'impossible' happened)
               -- (GHC version 8.6.5 for x86_64-unknown-linux):
               --       buildKindCoercion
               -- CLog 2 (n_a681K + m_a681L)
               -- CLog 2 n_a681K
               -- n_a681K + m_a681L
               -- n_a681K
               --
               -- down the line.
               --
               -- So while the "shape" of the KnownNat evidence that we return
               -- follows 'CLog 2 n + 1', the type of the evidence will be
               -- 'KnownNat fsk'; the one GHC originally asked us to solve.
               then return ((,concat new) <$> makeOpDictByFiat df cls args1N args0N (unOrig orig) evs)
               else return ((,concat new) <$> makeOpDict df cls args1N args0N (unOrig orig) evs)
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
    go_arg :: PredType -> TcPluginM 'Solve (EvExpr,[Ct])
#else
    go_arg :: PredType -> TcPluginM 'Solve (EvTerm,[Ct])
#endif
    go_arg ty = case lookup (CType ty) givens of
      Just ev -> return (ev,[])
      _ -> do
        (ev,wanted) <- makeWantedEv ct ty
        return (ev,[wanted])

    -- Fall through case: look up the normalised [W]anted constraint in the list
    -- of [G]iven constraints.
    go_other :: Type -> Maybe EvTerm
    go_other ty =
      let knClsTc = classTyCon cls
          kn      = mkTyConApp knClsTc [ty]
          cast    = if CType ty == CType op
#if MIN_VERSION_ghc(8,6,0)
                       then Just . EvExpr
#else
                       then Just
#endif
                       else makeKnCoercion cls ty op
      in  cast =<< lookup (CType kn) givens

    -- Find a known constraint for a wanted, so that (modulo normalization)
    -- the two are a constant offset apart.
    offset :: Type -> TcPluginM 'Solve (Maybe (EvTerm,[Ct]))
    offset LitTy{} = pure Nothing
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
          knownsX  = knowns ++ knownsR
          -- pair up the sum-of-products KnownNat constraints
          -- with the original Nat operation
          subWant  = mkTyConApp typeNatSubTyCon . (:[want])
          exploded = map (fst . runWriter . normaliseNat . subWant &&& id)
                         knownsX
          -- interesting cases for us are those where
          -- wanted and given only differ by a constant
          examineDiff (S [P [I n]]) entire = Just (entire,I n)
          examineDiff (S [P [V v]]) entire = Just (entire,V v)
          examineDiff _ _ = Nothing
          interesting = mapMaybe (uncurry examineDiff) exploded
      -- convert the first suitable evidence
      ((h,corr):_) <- pure interesting
      x <- case corr of
                I 0 -> pure h
                I i | i < 0
                    -> pure (mkTyConApp typeNatAddTyCon [h,mkNumLitTy (negate i)])
                    | otherwise
                    -> pure (mkTyConApp typeNatSubTyCon [h,mkNumLitTy i])
                -- If the offset between a given and a wanted is again the wanted
                -- then the given is twice the wanted; so we can just divide
                -- the given by two. Only possible in GHC 8.4+; for 8.2 we simply
                -- fail because we don't know how to divide.
                c   | CType (reifySOP (S [P [c]])) == CType want ->
#if MIN_VERSION_ghc(8,4,0)
                     pure (mkTyConApp typeNatDivTyCon [h,reifySOP (S [P [I 2]])])
#else
                     MaybeT (pure Nothing)
#endif
                -- Only solve with a variable offset if we have [G]iven knownnat for it
                -- Failing to do this check results in #30
                V v | all (not . eqType (TyVarTy v)) knownsX
                    -> MaybeT (pure Nothing)
                _ -> pure (mkTyConApp typeNatSubTyCon [h,reifySOP (S [P [corr]])])
      MaybeT (go x)

makeWantedEv
  :: Ct
  -> Type
#if MIN_VERSION_ghc(8,5,0)
  -> TcPluginM 'Solve (EvExpr,Ct)
#else
  -> TcPluginM 'Solve (EvTerm,Ct)
#endif
makeWantedEv ct ty = do
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
      ct_ls   = ctLocSpan (ctLoc ct)
      ctl     = ctEvLoc  wantedCtEv
      wanted' = setCtLoc wanted (setCtLocSpan ctl ct_ls)
  return (ev,wanted')

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
makeOpDict
  :: (Class,DFunId)
  -- ^ "magic" class function and dictionary function id
  -> Class
  -- ^ KnownNat class
  -> [Type]
  -- ^ Argument types for the Class
  -> [Type]
  -- ^ Argument types for the Instance
  -> Type           -- ^ Type of the result
#if MIN_VERSION_ghc(8,5,0)
  -> [EvExpr]
#else
  -> [EvTerm]
#endif
  -- ^ Evidence arguments
  -> Maybe EvTerm
makeOpDict (opCls,dfid) knCls tyArgsC tyArgsI z evArgs
  | Just (_, kn_co_dict) <- tcInstNewTyCon_maybe (classTyCon knCls) [z]
    -- KnownNat n ~ SNat n
  , [ kn_meth ] <- classMethods knCls
  , Just kn_tcRep <- tyConAppTyCon_maybe -- SNat
                      $ funResultTy      -- SNat n
                      $ dropForAlls      -- KnownNat n => SNat n
                      $ idType kn_meth   -- forall n. KnownNat n => SNat n
  , Just (_, kn_co_rep) <- tcInstNewTyCon_maybe kn_tcRep [z]
    -- SNat n ~ Integer
  , Just (_, op_co_dict) <- tcInstNewTyCon_maybe (classTyCon opCls) tyArgsC
    -- KnownNatAdd a b ~ SNatKn (a+b)
  , [ op_meth ] <- classMethods opCls
  , Just (op_tcRep,op_args) <- splitTyConApp_maybe        -- (SNatKn, [KnownNatF2 f x y])
                                 $ funResultTy            -- SNatKn (KnownNatF2 f x y)
                                 $ (`piResultTys` tyArgsC) -- KnownNatAdd f x y => SNatKn (KnownNatF2 f x y)
                                 $ idType op_meth         -- forall f a b . KnownNat2 f a b => SNatKn (KnownNatF2 f a b)
  , Just (_, op_co_rep) <- tcInstNewTyCon_maybe op_tcRep op_args
    -- SNatKn (a+b) ~ Integer
#if MIN_VERSION_ghc(8,5,0)
  , dfun_inst <- evDFunApp dfid tyArgsI evArgs
#else
  , let dfun_inst = EvDFunApp dfid tyArgsI evArgs
#endif
        -- KnownNatAdd a b
  , let op_to_kn  = mkTcTransCo (mkTcTransCo op_co_dict op_co_rep)
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
#else
               -> EvTerm
#endif
               -- ^ KnownNat dictionary for the argument
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
makeLitDict :: Class -> Type -> Integer -> TcPluginM 'Solve (Maybe EvTerm)
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
#if MIN_VERSION_ghc(9,0,0)
    let et = mkNaturalExpr i
#else
    et <- unsafeTcPluginTcM (mkNaturalExpr i)
#endif
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

{- |
Given:

* A "magic" class, and corresponding instance dictionary function, for a
  type-level boolean operation
* Two KnownBool dictionaries

makeOpDictByFiat instantiates the dictionary function with the KnownBool
dictionaries, and coerces it to a KnownBool dictionary. i.e. for KnownBoolNat2,
the "magic" dictionary for binary functions, the coercion happens in the
following steps:

1. KnownBoolNat2 "<=?" x y     -> SBoolF "<=?"
2. SBoolF "<=?"                -> Bool
3. Bool                        -> SNat (x <=? y)  THE BY FIAT PART!
4. SBool (x <=? y)             -> KnownBool (x <=? y)

this process is mirrored for the dictionary functions of a higher arity
-}
makeOpDictByFiat
  :: (Class,DFunId)
  -- ^ "magic" class function and dictionary function id
  -> Class
   -- ^ KnownNat class
  -> [Type]
  -- ^ Argument types for the Class
  -> [Type]
  -- ^ Argument types for the Instance
  -> Type
  -- ^ Type of the result
#if MIN_VERSION_ghc(8,6,0)
  -> [EvExpr]
#else
  -> [EvTerm]
#endif
  -- ^ Evidence arguments
  -> Maybe EvTerm
#if MIN_VERSION_ghc(8,6,0)
makeOpDictByFiat (opCls,dfid) knCls tyArgsC tyArgsI z evArgs
    -- KnownBool b ~ SBool b
  | Just (_, kn_co_dict) <- tcInstNewTyCon_maybe (classTyCon knCls) [z]
  , [ kn_meth ] <- classMethods knCls
  , Just kn_tcRep <- tyConAppTyCon_maybe -- SBool
                       $ funResultTy     -- SBool b
                       $ dropForAlls     -- KnownBool b => SBool b
                       $ idType kn_meth  -- forall b. KnownBool b => SBool b
    -- SBool b R~ Bool (The "Lie")
  , let kn_co_rep = mkUnivCo (PluginProv "ghc-typelits-knownnat")
                             Representational
                             (mkTyConApp kn_tcRep [z]) boolTy
    -- KnownBoolNat2 f a b ~ SBool f
  , Just (_, op_co_dict) <- tcInstNewTyCon_maybe (classTyCon opCls) tyArgsC
  , [ op_meth ] <- classMethods opCls
  , Just (op_tcRep,op_args) <- splitTyConApp_maybe        -- (SBool, [f])
                                 $ funResultTy            -- SBool f
                                 $ (`piResultTys` tyArgsC) -- KnownBoolNat2 f x y => SBool f
                                 $ idType op_meth         -- forall f x y . KnownBoolNat2 f a b => SBoolf f
    -- SBoolF f ~ Bool
  , Just (_, op_co_rep) <- tcInstNewTyCon_maybe op_tcRep op_args
  , dfun_inst <- evDFunApp dfid tyArgsI evArgs
    -- KnownBoolNat2 f x y ~ KnownBool b
  , let op_to_kn  = mkTcTransCo (mkTcTransCo op_co_dict op_co_rep)
                                (mkTcSymCo (mkTcTransCo kn_co_dict kn_co_rep))
        ev_tm     = mkEvCast dfun_inst op_to_kn
  = Just ev_tm
  | otherwise
  = Nothing
#else
makeOpDictByFiat _ _ _ _ _ _ = Nothing
#endif
