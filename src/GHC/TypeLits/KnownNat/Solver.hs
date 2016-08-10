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

The plugin can only derive @KnownNat@ constraints consisting of:

* Type-level naturals
* Type variables
* Applications of the arithmetic expression: @{+,*,^}@

i.e. it /cannot/ derive a @KnownNat (n-1)@ constraint from a @KnownNat n@
constraint

To use the plugin, add the

@
OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver
@

Pragma to the header of your file.

-}

{-# LANGUAGE TupleSections #-}

{-# LANGUAGE Trustworthy   #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module GHC.TypeLits.KnownNat.Solver (plugin) where

-- external
import Data.Maybe          (catMaybes,mapMaybe)
import GHC.TcPluginM.Extra (lookupModule, lookupName, tracePlugin)

-- GHC API
import Class      (Class, classMethods, className, classTyCon)
import FamInst    (tcInstNewTyCon_maybe)
import FastString (fsLit)
import Id         (idType)
import InstEnv    (instanceDFunId,lookupUniqueInstEnv)
import Module     (mkModuleName)
import OccName    (mkTcOcc)
import Outputable (Outputable (..), (<+>), integer, text, vcat, parens)
import Panic      (panicDoc, pgmErrorDoc)
import Plugins    (Plugin (..), defaultPlugin)
import PrelNames  (knownNatClassName)
import TcEvidence (EvTerm (..), EvLit (EvNum), mkEvCast, mkTcSymCo, mkTcTransCo)
import TcPluginM  (TcPluginM, tcLookupClass, getInstEnvs, zonkCt)
import TcRnTypes  (Ct, CtEvidence (..), TcPlugin(..), TcPluginResult (..),
                   ctEvidence, ctEvPred, isWanted)
import TcTypeNats (typeNatAddTyCon, typeNatMulTyCon, typeNatExpTyCon)
import Type       (PredTree (ClassPred), TyVar, classifyPredType, dropForAlls,
                   funResultTy, tyConAppTyCon_maybe, mkNumLitTy, mkTyVarTy,
                   mkTyConApp)
import TyCoRep    (Type (..), TyLit (..))
import Var        (DFunId)

-- | Classes and instances from "GHC.TypeLits.KnownNat"
data KnownNatDefs = KnownNatDefs
  { knAddDFunId :: (Class,DFunId) -- ^ KnownNatAdd class and its only instance
  , knMulDFunId :: (Class,DFunId) -- ^ KnownNatMul class and its only instance
  , knExpDFunId :: (Class,DFunId) -- ^ KnownNatPow class and its only instance
  }

instance Outputable KnownNatDefs where
  ppr d = text "{" <+> ppr (knAddDFunId d) <+>
          text "," <+> ppr (knMulDFunId d) <+>
          text "," <+> ppr (knExpDFunId d) <+>
          text "}"

-- | KnownNat constraints
type KnConstraint = (Ct    -- The constraint
                    ,Class -- KnownNat class
                    ,KnOp  -- The argument to KnownNat
                    )

-- | Reified argument of a KnownNat
data KnOp
  = I Integer
  | V TyVar
  | Add KnOp KnOp
  | Mul KnOp KnOp
  | Exp KnOp KnOp

instance Outputable KnOp where
  ppr (I i)     = integer i
  ppr (V v)     = ppr v
  ppr (Add x y) = parens $ ppr x <+> text "+" <+> ppr y
  ppr (Mul x y) = parens $ ppr x <+> text "*" <+> ppr y
  ppr (Exp x y) = parens $ ppr x <+> text "^" <+> ppr y

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

The plugin can only derive @KnownNat@ constraints consisting of:

* Type-level naturals
* Type variables
* Applications of the arithmetic expression: @{+,*,^}@.

i.e. it /cannot/ derive a @KnownNat (n-1)@ constraint from a @KnownNat n@
constraint

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
      kn_givens <- catMaybes <$> mapM (fmap toKnConstraint . zonkCt) givens
      -- Make a lookup table of the [G]iven KnownNat constraints
      let kn_map = mapMaybe toKnEntry kn_givens
      -- Try to solve the wanted KnownNat constraints given the [G]iven
      -- KnownNat constraints
      let solved = mapMaybe (constraintToEvTerm defs kn_map) kn_wanteds
      return (TcPluginOk solved [])

-- | Get the KnownNat constraints
toKnConstraint :: Ct -> Maybe KnConstraint
toKnConstraint ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
  ClassPred cls [ty]
    |  className cls == knownNatClassName
    -> ((ct,cls,) <$> toKnOp ty)
  _ -> Nothing

{- |
The plugin can only derive @KnownNat@ constraints consisting of:

* Type-level naturals
* Type variables
* Applications of the arithmetic expression: @{+,*,^}@.
-}
toKnOp :: Type -> Maybe KnOp
toKnOp (LitTy (NumTyLit i)) = pure (I i)
toKnOp (TyVarTy v)          = pure (V v)
toKnOp (TyConApp tc [x,y])
  | tc == typeNatAddTyCon = Add <$> toKnOp x <*> toKnOp y
  | tc == typeNatMulTyCon = Mul <$> toKnOp x <*> toKnOp y
  | tc == typeNatExpTyCon = Exp <$> toKnOp x <*> toKnOp y
toKnOp _ = Nothing

-- | Create a look-up entry for @n@ given a [G]iven @KnownNat n@ constraint.
toKnEntry :: KnConstraint -> Maybe (TyVar,KnConstraint)
toKnEntry kn@(_,_,V v) = Just (v,kn)
toKnEntry _ = Nothing

-- | Find the \"magic\" classes and instances in "GHC.TypeLits.KnownNat"
lookupKnownNatDefs :: TcPluginM KnownNatDefs
lookupKnownNatDefs = do
    md     <- lookupModule myModule myPackage
    addDF  <- look md "KnownNatAdd"
    mulDF  <- look md "KnownNatMul"
    expDF  <- look md "KnownNatExp"
    return $ KnownNatDefs addDF mulDF expDF
  where
    look md s = do
      nm   <- lookupName md (mkTcOcc s)
      cls  <- tcLookupClass nm
      ienv <- getInstEnvs
      case lookupUniqueInstEnv ienv cls [mkNumLitTy 0, mkNumLitTy 0] of
        Right (inst, _) -> return (cls,instanceDFunId inst)
        Left  err       ->
          pgmErrorDoc "Initialising GHC.TypeLits.KnownNat.Solver failed"
                      (vcat [text "Cannot find: " <+> text s
                            ,text "Reason: "
                            ,err
                            ])

    myModule  = mkModuleName "GHC.TypeLits.KnownNat"
    myPackage = fsLit "ghc-typelits-knownnat"

-- | Convert a reified argument of a KnownNat constraint back to a type
reifyOp :: KnOp -> Type
reifyOp (I i)     = mkNumLitTy i
reifyOp (V v)     = mkTyVarTy v
reifyOp (Add x y) = mkTyConApp typeNatAddTyCon [reifyOp x, reifyOp y]
reifyOp (Mul x y) = mkTyConApp typeNatMulTyCon [reifyOp x, reifyOp y]
reifyOp (Exp x y) = mkTyConApp typeNatExpTyCon [reifyOp x, reifyOp y]

-- | Try to create evidence for a wanted constraint
constraintToEvTerm :: KnownNatDefs -> [(TyVar,KnConstraint)] -> KnConstraint
                   -> Maybe (EvTerm,Ct)
constraintToEvTerm defs kn_map (ct,cls,op) = (,ct) <$> go op
  where
    go (I i) = makeLitDict cls (mkNumLitTy i) i
    go (V v) = case lookup v kn_map of
      Just (ct',_,_) -> let ct_ev = ctEvidence ct'
                            evT   = ctev_evar ct_ev
                        in  Just (EvId evT)
      Nothing -> Nothing
    go e = do
      let (x,y,df) = case e of
            Add x' y' -> (x',y',knAddDFunId defs)
            Mul x' y' -> (x',y',knMulDFunId defs)
            Exp x' y' -> (x',y',knExpDFunId defs)
            _ -> panicDoc "GHC.TypeLits.KnownNat.Solver: not an op" (ppr e)
      x' <- go x
      y' <- go y
      makeOpDict df cls (reifyOp x) (reifyOp y) (reifyOp e) x' y'

{-
Given:

* A "magic" class, and corresponding instance dictionary function, for a
  type-level arithmetic operation
* Two KnownNat dictionaries

makeOpDict instantiates the dictionary function with the KnownNat dictionaries,
and coerces it to a KnownNat dictionary. i.e. for KnownNatAdd, the "magic"
dictionary for addition, the coercion happens in the following steps:

1. KnownNatAdd a b -> SNatKn (a + b)
2. SNatKn (a + b)  -> Integer
3. Integer         -> SNat (a + b)
4. SNat (a + b)    -> KnownNat (a + b)

The process is mirrored for KnownNatMul, and KnownNatExp, the classes
representing multiplication and exponentiation.
-}
makeOpDict :: (Class,DFunId) -- ^ "magic" class function and dictionary function id
           -> Class          -- ^ KnownNat class
           -> Type           -- ^ Type of the first argument
           -> Type           -- ^ Type of the second argument
           -> Type           -- ^ Type of the result
           -> EvTerm         -- ^ KnownNat dictionary for the first argument
           -> EvTerm         -- ^ KnownNat dictionary for the second argument
           -> Maybe EvTerm
makeOpDict (opCls,dfid) knCls x y z xEv yEv
  | Just (_, kn_co_dict) <- tcInstNewTyCon_maybe (classTyCon knCls) [z]
    -- KnownNat n ~ SNat n
  , [ kn_meth ] <- classMethods knCls
  , Just kn_tcRep <- tyConAppTyCon_maybe -- SNat
                      $ funResultTy      -- SNat n
                      $ dropForAlls      -- KnownNat n => SNat n
                      $ idType kn_meth   -- forall n. KnownNat n => SNat n
  , Just (_, kn_co_rep) <- tcInstNewTyCon_maybe kn_tcRep [z]
    -- SNat n ~ Integer
  , Just (_, op_co_dict) <- tcInstNewTyCon_maybe (classTyCon opCls) [x,y]
    -- KnownNatAdd a b ~ SNatKn (a+b)
  , [ op_meth ] <- classMethods opCls
  , Just op_tcRep <- tyConAppTyCon_maybe -- SNatKn
                      $ funResultTy      -- SNatKn (a+b)
                      $ dropForAlls      -- KnownNatAdd a b => SNatKn (a + b)
                      $ idType op_meth   -- forall a b . KnownNatAdd a b => SNatKn (a+b)
  , Just (_, op_co_rep) <- tcInstNewTyCon_maybe op_tcRep [z]
    -- SNatKn (a+b) ~ Integer
  , let dfun_inst = EvDFunApp dfid [x,y] [xEv,yEv]
        -- KnownNatAdd a b
        op_to_kn  = mkTcTransCo (mkTcTransCo op_co_dict op_co_rep)
                                (mkTcSymCo (mkTcTransCo kn_co_dict kn_co_rep))
        -- KnownNatAdd a b ~ KnownNat (a+b)
        ev_tm     = mkEvCast dfun_inst op_to_kn
  = Just ev_tm
  | otherwise
  = Nothing

-- | THIS CODE IS COPIED FROM:
-- https://github.com/ghc/ghc/blob/8035d1a5dc7290e8d3d61446ee4861e0b460214e/compiler/typecheck/TcInteract.hs#L1973
--
-- makeLitDict adds a coercion that will convert the literal into a dictionary
-- of the appropriate type.  See Note [KnownNat & KnownSymbol and EvLit]
-- in TcEvidence.  The coercion happens in 2 steps:
--
--     Integer -> SNat n     -- representation of literal to singleton
--     SNat n  -> KnownNat n -- singleton to dictionary
makeLitDict :: Class -> Type -> Integer -> Maybe EvTerm
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
  , let ev_tm = mkEvCast (EvLit (EvNum i)) (mkTcSymCo (mkTcTransCo co_dict co_rep))
  = Just ev_tm
  | otherwise
  = Nothing
