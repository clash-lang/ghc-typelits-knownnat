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

{-# LANGUAGE BangPatterns  #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE MultiWayIf    #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns  #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

{-# LANGUAGE Trustworthy   #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module GHC.TypeLits.KnownNat.Solver
  ( plugin )
where

-- base
import Control.Arrow
  ( (&&&), first )
import Data.Maybe
  ( catMaybes, fromMaybe, mapMaybe )

-- transformers
import Control.Monad.Trans.Maybe
  ( MaybeT (..) )
import Control.Monad.Trans.Writer.Strict

-- ghc-typelits-natnormalise
import GHC.TypeLits.Normalise.SOP
  ( SOP (..), Product (..), Symbol (..) )
import GHC.TypeLits.Normalise.Unify
  ( CType (..),normaliseNat, reifySOP, CoreSOP )

-- ghc-tcplugin-api
import GHC.TcPlugin.API
import GHC.TcPlugin.API.TyConSubst

-- ghc-typelits-knownnat
import GHC.TypeLits.KnownNat.Compat
  ( KnownNatDefs(..), lookupKnownNatDefs, mkNaturalExpr
  , coercionRKind, classMethodTy
  , irrelevantMult
  )

-- ghc
import GHC.Builtin.Names
  ( knownNatClassName )
#if MIN_VERSION_ghc(9,1,0)
import GHC.Builtin.Types
  ( promotedFalseDataCon, promotedTrueDataCon )
import GHC.Builtin.Types.Literals
  ( typeNatCmpTyCon )
#endif
import GHC.Builtin.Types.Literals
  ( typeNatAddTyCon, typeNatDivTyCon, typeNatSubTyCon )
import GHC.Core
  ( mkApps, mkTyApps )
import GHC.Core.Class
  ( classMethods, classTyVars )
import GHC.Core.Coercion
  ( instNewTyCon_maybe, mkNomReflCo, mkTyConAppCo )
import GHC.Core.DataCon
  ( dataConWrapId )
import GHC.Core.InstEnv
  ( instanceDFunId, lookupUniqueInstEnv )
import GHC.Core.TyCo.Rep
  ( Type(..), TyLit(..) )
import GHC.Core.TyCo.Subst
  ( substTyWithUnchecked )
import GHC.Core.Type
  ( piResultTys, splitFunTys )
import GHC.Core.Utils
  ( exprType, mkCast )
import GHC.Driver.Plugins
  ( Plugin (..), defaultPlugin, purePlugin )
import GHC.Plugins
  ( HasDebugCallStack )
import GHC.Tc.Types.Evidence
  ( evTermCoercion_maybe, evSelector )
import GHC.Types.Id
  ( idType )
import GHC.Types.Name
  ( nameModule_maybe, nameOccName )
import GHC.Types.Name.Occurrence
  ( occNameString )
import GHC.Types.Var
  ( DFunId )
import GHC.Unit.Module
  ( moduleName, moduleNameString )
import GHC.Utils.Outputable
  ( (<+>), vcat, text )

--------------------------------------------------------------------------------

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
  { tcPlugin = \ _ -> Just $ mkTcPlugin normalisePlugin
  , pluginRecompile = purePlugin
  }

normalisePlugin :: TcPlugin
normalisePlugin =
  TcPlugin { tcPluginInit  = lookupKnownNatDefs
           , tcPluginSolve = solveKnownNat
           , tcPluginRewrite = const emptyUFM
           , tcPluginStop  = const (return ())
           }

solveKnownNat :: KnownNatDefs -> [Ct] -> [Ct]
              -> TcPluginM Solve TcPluginSolveResult
solveKnownNat _defs _givens []      = return (TcPluginOk [] [])
solveKnownNat defs  givens  wanteds = do
  let givensTyConSubst = mkTyConSubst givens
      kn_wanteds = map (\(x,y,z,orig) -> (x,y,z,orig))
                 $ mapMaybe (toKnConstraint defs) wanteds
  case kn_wanteds of
    [] -> return (TcPluginOk [] [])
    _  -> do
      -- Make a lookup table for all the [G]iven constraints
      let given_map = map toGivenEntry givens

      -- Try to solve the wanted KnownNat constraints given the [G]iven
      -- KnownNat constraints
      (solved,new) <- (unzip . catMaybes) <$> (mapM (constraintToEvTerm defs givensTyConSubst given_map) kn_wanteds)
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
toGivenEntry :: Ct -> (CType,EvExpr)
toGivenEntry ct = let ct_ev = ctEvidence ct
                      c_ty  = ctEvPred   ct_ev
                      ev    = ctEvExpr   ct_ev
                  in  (CType c_ty,ev)

-- | Try to create evidence for a wanted constraint
constraintToEvTerm
  :: KnownNatDefs
  -- ^ The "magic" KnownNatN classes
  -> TyConSubst
  -> [(CType,EvExpr)]
  -- ^ All the [G]iven constraints
  -> KnConstraint
  -> TcPluginM Solve (Maybe ((EvTerm,Ct),[Ct]))
constraintToEvTerm defs givensTyConSubst givens (ct,cls,op,orig) = do
    -- 1. Determine if we are an offset apart from a [G]iven constraint
    offsetM <- offset op
    evM     <- case offsetM of
                 -- 3.a If so, we are done
                 found@Just {} -> return found
                 -- 3.b If not, we check if the outer type-level operation
                 -- has a corresponding KnownNat<N> instance.
                 _ -> go (op,Nothing)
    return ((first (,ct)) <$> evM)
  where
    -- Determine whether the outer type-level operation has a corresponding
    -- KnownNat<N> instance, where /N/ corresponds to the arity of the
    -- type-level operation
    go :: (Type, Maybe Coercion) -> TcPluginM Solve (Maybe (EvTerm,[Ct]))
    go (go_other -> Just ev, _) = return (Just (ev,[]))
    go (ty@(TyConApp tc args0), sM)
      | let tcNm = tyConName tc
      , Just m <- nameModule_maybe tcNm
      = do
        ienv <- getInstEnvs
        let mS  = moduleNameString (moduleName m)
            tcS = occNameString (nameOccName tcNm)
            fn0 = mS ++ "." ++ tcS
            fn1 = mkStrLitTy (fsLit fn0)
            args1 = fn1:args0
            instM =
              if | Just knN_cls    <- knownNatN defs (length args0)
                 , Right (inst, _) <- lookupUniqueInstEnv ienv knN_cls args1
                 -> Just (inst,knN_cls,args0,args1)
  -- TODO: we should re-use the parsing functionality
  -- that is in GHC.TypeLits.NatNormalise.Compat.
#if MIN_VERSION_ghc(9,1,0)
                 | tc == ordCondTyCon defs
                 , [_,cmpNat,TyConApp t1 [],TyConApp t2 [],TyConApp f1 []] <- args0
                 , TyConApp cmpNatTc args2@(arg2:_) <- cmpNat
                 , cmpNatTc == typeNatCmpTyCon
                 , t1 == promotedTrueDataCon
                 , t2 == promotedTrueDataCon
                 , f1 == promotedFalseDataCon
                 , let knN_cls = knownBoolNat2 defs
                       ki      = typeKind arg2
                       args1N  = ki:fn1:args2
                 , Right (inst,_) <- lookupUniqueInstEnv ienv knN_cls args1N
                 -> Just (inst,knN_cls,args2,args1N)
#endif
                 | [arg0,_] <- args0
                 , let knN_cls = knownBoolNat2 defs
                       ki      = typeKind arg0
                       args1N  = ki:args1
                 , Right (inst, _) <- lookupUniqueInstEnv ienv knN_cls args1N
                 -> Just (inst,knN_cls,args0,args1N)
                 | (arg0:args0Rest@[_,_,_]) <- args0
                 , tc == ifTyCon defs
                 , let args1N = arg0:fn1:args0Rest
                       knN_cls = knownNat2Bool defs
                 , Right (inst, _) <- lookupUniqueInstEnv ienv knN_cls args1N
                 -> Just (inst,knN_cls,args0Rest,args1N)
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
                deps :: [Coercion]
                deps = [] -- XXX TODO: not declaring dependency on outer Givens
            (evs,new) <- unzip <$> mapM (go_arg . irrelevantMult) df_args
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
               then return ((,concat new) <$> makeOpDictByFiat df cls args1N args0N (unOrig orig) deps evs)
               else return ((,concat new) <$> makeOpDict df cls args1N args0N (unOrig orig) deps evs (fmap (ty,) sM))
          _ -> return ((,[]) <$> go_other ty)

    go ((LitTy (NumTyLit i)), _)
      -- Let GHC solve simple Literal constraints
      | LitTy _ <- op
      = return Nothing
      -- This plugin only solves Literal KnownNat's that needed to be normalised
      -- first
      | otherwise
      = (fmap (,[])) <$> makeLitDict cls op [] i -- XXX: ok to pass empty dependent coercions?
    go _ = return Nothing

    -- Get EvTerm arguments for type-level operations. If they do not exist
    -- as [G]iven constraints, then generate new [W]anted constraints
    go_arg :: PredType -> TcPluginM Solve (EvExpr,[Ct])
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
                       then Just . EvExpr
                       else makeKnCoercion cls ty op [] -- XXX: ok to pass empty dependent coercions?
      in  cast =<< lookup (CType kn) givens

    -- Find a known constraint for a wanted, so that (modulo normalization)
    -- the two are a constant offset apart.
    offset :: Type -> TcPluginM Solve (Maybe (EvTerm,[Ct]))
    offset LitTy{} = pure Nothing
    offset want = runMaybeT $ do
      let -- Get the knownnat contraints
          unKn ty' = case classifyPredType ty' of
                       ClassPred cls' [ty'']
                         | className cls' == knownNatClassName
                         -> Just ty''
                       _ -> Nothing
          -- Get the rewrites
          unEq (ty',ev) = case classifyPredType ty' of
                            EqPred NomEq ty1 ty2 -> Just (ty1,ty2,ev)
                            _ -> Nothing
          rewrites :: [(Type,Type,EvExpr)]
          rewrites = mapMaybe (unEq . first unCType) givens
          -- Rewrite
          rewriteTy tyK (ty1,ty2,ev)
            | ty1 `eqType` tyK
            = Just (ty2,Just (tyK,evTermCoercion_maybe (EvExpr ev)))
            | ty2 `eqType` tyK
            = Just (ty1,Just (tyK,fmap mkSymCo (evTermCoercion_maybe (EvExpr ev))))
            | otherwise
            = Nothing
          -- Get only the [G]iven KnownNat constraints
          knowns   = mapMaybe (unKn . unCType . fst) givens
          -- Get all the rewritten KNs
          knownsR  = catMaybes $ concatMap (\t -> map (rewriteTy t) rewrites) knowns
          knownsX :: [(Type, Maybe (Type, Maybe Coercion))]
          knownsX  = fmap (,Nothing) knowns ++ knownsR
          -- pair up the sum-of-products KnownNat constraints
          -- with the original Nat operation
          subWant  = mkTyConApp typeNatSubTyCon . (:[want])
          -- exploded :: [()]
          exploded = map (discardCo . runWriter . normaliseNat givensTyConSubst . subWant . fst &&& id)
                         knownsX
          -- XXX TODO: discarding coercions produced by 'normaliseNat'
          discardCo :: ((CoreSOP, [Coercion]), [(Type, Type)]) -> CoreSOP
          discardCo ((a, _co), _) = a
          -- interesting cases for us are those where
          -- wanted and given only differ by a constant
          examineDiff (S [P [I n]]) entire = Just (entire,I n)
          examineDiff (S [P [V v]]) entire = Just (entire,V v)
          examineDiff _ _ = Nothing
          interesting = mapMaybe (uncurry examineDiff) exploded
      -- convert the first suitable evidence
      (((h,sM),corr):_) <- pure interesting
      x <- case corr of
                I 0 -> pure (fromMaybe (h,Nothing) sM)
                I i | i < 0
                    , let l1 = mkNumLitTy (negate i)
                    -> case sM of
                        Just (q,cM) -> pure
                          ( mkTyConApp typeNatAddTyCon [q,l1]
                          , fmap (mkTyConAppCo Nominal typeNatAddTyCon . (:[mkNomReflCo l1])) cM
                          )
                        Nothing -> pure
                          ( mkTyConApp typeNatAddTyCon [h,l1]
                          , Nothing
                          )
                    | otherwise
                    , let l1 = mkNumLitTy i
                    -> case sM of
                        Just (q,cM) -> pure
                          ( mkTyConApp typeNatSubTyCon [q,l1]
                          , fmap (mkTyConAppCo Nominal typeNatSubTyCon . (:[mkNomReflCo l1])) cM
                          )
                        Nothing -> pure
                          ( mkTyConApp typeNatSubTyCon [h,l1]
                          , Nothing
                          )
                -- If the offset between a given and a wanted is again the wanted
                -- then the given is twice the wanted; so we can just divide
                -- the given by two. Only possible in GHC 8.4+; for 8.2 we simply
                -- fail because we don't know how to divide.
                c   | CType (reifySOP (S [P [c]])) == CType want
                    , let l2 = mkNumLitTy 2
                    -> case sM of
                        Just (q,cM) -> pure
                          ( mkTyConApp typeNatDivTyCon [q,l2]
                          , fmap (mkTyConAppCo Nominal typeNatDivTyCon . (:[mkNomReflCo l2])) cM
                          )
                        Nothing -> pure
                          ( mkTyConApp typeNatDivTyCon [h,l2]
                          , Nothing
                          )
                -- Only solve with a variable offset if we have [G]iven knownnat for it
                -- Failing to do this check results in #30
                V v  | all (not . eqType (TyVarTy v) . fst) knownsX
                     -> MaybeT (pure Nothing)
                _    -> let lC = reifySOP (S [P [corr]]) in
                        case sM of
                          Just (q,cM) -> pure
                            ( mkTyConApp typeNatSubTyCon [q,lC]
                            , fmap (mkTyConAppCo Nominal typeNatSubTyCon . (:[mkNomReflCo lC])) cM
                            )
                          Nothing -> pure
                            ( mkTyConApp typeNatSubTyCon [h,lC]
                            , Nothing
                            )
      MaybeT (go x)

makeWantedEv
  :: Ct
  -> Type
  -> TcPluginM Solve (EvExpr,Ct)
makeWantedEv ct ty = do
  -- Create a new wanted constraint
  wantedCtEv <- newWanted (ctLoc ct) ty
  let ev      = ctEvExpr wantedCtEv
      wanted  = mkNonCanonical wantedCtEv
  return (ev,wanted)

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
  -> Type
  -- ^ Type of the result
  -> [Coercion]
  -- ^ Dependent coercions
  -> [EvExpr]
  -- ^ Evidence arguments
  -> Maybe (Type, Coercion)
  -> Maybe EvTerm
makeOpDict (opCls,dfid) knCls tyArgsC tyArgsI z deps evArgs sM
  | let z1 = maybe z fst sM
    -- SNatKn (a+b) ~ Integer
  , let dfun_inst = evDFunApp dfid tyArgsI evArgs
        -- KnownNatAdd a b
  , let op_to_kn :: EvExpr -> EvExpr
        op_to_kn ev
            = wrapUnaryClassByFiat knCls [z1] deps
            $ unwrapUnaryClassOverNewtype opCls tyArgsC ev
        -- KnownNatAdd a b ~ KnownNat (a+b)
  , let op_to_kn1 ev = case sM of
          Nothing -> op_to_kn ev
          Just (_,rw) ->
            let kn_co_rw = mkTyConAppCo Representational (classTyCon knCls) [rw]
                kn_co_co = mkPluginUnivCo "ghc-typelits-knownnat" Representational
                              deps
                              (coercionRKind kn_co_rw)
                              (mkTyConApp (classTyCon knCls) [z])
              in mkCast (op_to_kn ev) (mkTransCo kn_co_rw kn_co_co)
  = Just $ EvExpr $ op_to_kn1 dfun_inst

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
               -> [Coercion]     -- ^ Dependent coercions
               -> EvExpr
               -- ^ KnownNat dictionary for the argument
               -> Maybe EvTerm
makeKnCoercion knCls x z deps knownNat_x
  = Just $ EvExpr $ wrapUnaryClassByFiat knCls [z] deps
                  $ unwrapUnaryClassOverNewtype knCls [x] knownNat_x

-- | THIS CODE IS COPIED FROM:
-- https://github.com/ghc/ghc/blob/8035d1a5dc7290e8d3d61446ee4861e0b460214e/compiler/typecheck/TcInteract.hs#L1973
--
-- makeLitDict adds a coercion that will convert the literal into a dictionary
-- of the appropriate type.  See Note [KnownNat & KnownSymbol and EvLit]
-- in TcEvidence.  The coercion happens in 2 steps:
--
--     Integer -> SNat n     -- representation of literal to singleton
--     SNat n  -> KnownNat n -- singleton to dictionary
makeLitDict :: Class
            -> Type
            -> [Coercion]
                 -- ^ dependent coercions
            -> Integer
            -> TcPluginM Solve (Maybe EvTerm)
makeLitDict clas ty deps i
  = do
    et <- mkNaturalExpr i
    let
      ev_tm = wrapUnaryClassByFiat clas [ty] deps et
    return (Just $ EvExpr ev_tm)

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
  -> [Coercion]
  -- ^ Dependent coercions
  -> [EvExpr]
  -- ^ Evidence arguments
  -> Maybe EvTerm
makeOpDictByFiat (opCls,dfid) knCls tyArgsC tyArgsI z deps evArgs
  = Just $ EvExpr $ wrapUnaryClassByFiat knCls [z] deps
                  $ unwrapUnaryClassOverNewtype opCls tyArgsC ev0
  where
    ev0 = evDFunApp dfid tyArgsI evArgs

-- | Given a class of the form @class C a b c where { meth :: ... }@ with
-- a single method, construct a dictionary of the class using an 'UnivCo'.
wrapUnaryClassByFiat :: HasDebugCallStack => Class -> [Type] -> [Coercion] -> EvExpr -> EvExpr
wrapUnaryClassByFiat cls tys deps et
  | Just dc <- tyConSingleDataCon_maybe (classTyCon cls)
  , [meth] <- classMethods cls
  , let meth_ty = subst $ classMethodTy meth
  = let
      by_fiat =
        mkPluginUnivCo "ghc-typelits-knownnat" Representational
          deps
          (exprType et)
          meth_ty
    in
      Var (dataConWrapId dc) `mkTyApps` tys `mkApps` [mkCast et by_fiat]
  | otherwise
  = pprPanic "wrapUnaryClassByFiat: class not of expected form" $
      vcat [ text "cls:" <+> ppr cls
           , text "tys:" <+> ppr tys
           ]

  where
    subst = substTyWithUnchecked (classTyVars cls) tys

-- | Given a class of the form @class C a b c where { meth :: N x y }@
-- in which @N@ is a newtype, and a dictionary for this class, unwraps **both**
-- the class and the newtype to obtain the value inside the newtype.
unwrapUnaryClassOverNewtype :: HasDebugCallStack => Class -> [Type] -> EvExpr -> EvExpr
unwrapUnaryClassOverNewtype cls tys et
  | [sel] <- classMethods cls
  , Just (rep_tc, rep_args) <- splitTyConApp_maybe (subst $ classMethodTy sel)
  , Just (_, co) <- instNewTyCon_maybe rep_tc rep_args
  = mkCast (evSelector sel tys [et]) co
  | otherwise
  = pprPanic "unwrapUnaryClassOverNewtype: class not of expected form" $
      vcat [ text "cls:" <+> ppr cls
           , text "tys:" <+> ppr tys
           ]
  where
    subst = substTyWithUnchecked (classTyVars cls) tys
