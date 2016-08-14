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
* Type variables, when there is a matching given @KnownNat@ constraint
* Applications of the arithmetic expression: @{+,*,^}@; i.e. it /cannot/ derive
  a @KnownNat (n-1)@ constraint given a @KnownNat n@ constraint
* All other types, when there is a matching given @KnownNat@ constraint; i.e.
  It /can/ derive a @KnownNat (Max x y + 1)@ constraint given a
  @KnownNat (Max x y)@ constraint.

To use the plugin, add the

@
OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver
@

Pragma to the header of your file.

-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections              #-}

{-# LANGUAGE Trustworthy   #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module GHC.TypeLits.KnownNat.Solver (plugin) where

-- external
import Control.Arrow             (first)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.Coerce               (coerce)
import Data.Maybe                (catMaybes,mapMaybe)
import GHC.TcPluginM.Extra       (lookupModule, lookupName, tracePlugin)

-- GHC API
import Class      (Class, classMethods, className, classTyCon)
import FamInst    (tcInstNewTyCon_maybe)
import FastString (fsLit)
import Id         (idType)
import InstEnv    (instanceDFunId,lookupUniqueInstEnv)
import Module     (mkModuleName)
import OccName    (mkTcOcc)
import Outputable (Outputable (..), (<+>), text)
import Plugins    (Plugin (..), defaultPlugin)
import PrelNames  (knownNatClassName)
import TcEvidence (EvTerm (..), EvLit (EvNum), mkEvCast, mkTcSymCo, mkTcTransCo)
import TcPluginM  (TcPluginM, tcLookupClass, getInstEnvs, zonkCt)
import TcRnTypes  (Ct, CtEvidence (..), TcPlugin(..), TcPluginResult (..),
                   ctEvidence, ctEvPred, isWanted)
import Type       (PredTree (ClassPred), classifyPredType, dropForAlls, eqType,
                   funResultTy, tyConAppTyCon_maybe, mkNumLitTy)
import TyCoRep    (Type (..), TyLit (..))
import Var        (DFunId, EvVar)

import TyCon      (tyConName)
import Type       (mkStrLitTy)
import Module     (moduleName, moduleNameString)
import Name       (nameModule_maybe, nameOccName)
import OccName    (occNameString)

-- | Classes and instances from "GHC.TypeLits.KnownNat"
data KnownNatDefs = KnownNatDefs
  { kn2 :: Class -- ^ KnownNat2 class
  }

instance Outputable KnownNatDefs where
  ppr d = text "{" <+> ppr (kn2 d) <+>
          text "}"

-- | KnownNat constraints
type KnConstraint = (Ct    -- The constraint
                    ,Class -- KnownNat class
                    ,Type  -- The argument to KnownNat
                    )

newtype CType = CType Type
  deriving Outputable

instance Eq CType where
  (==) = coerce eqType

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
* Type variables, when there is a matching given @KnownNat@ constraint
* Applications of the arithmetic expression: @{+,*,^}@; i.e. it /cannot/ derive
  a @KnownNat (n-1)@ constraint given a @KnownNat n@ constraint
* All other types, when there is a matching given @KnownNat@ constraint; i.e.
  It /can/ derive a @KnownNat (Max x y + 1)@ constraint given a
  @KnownNat (Max x y)@ constraint.

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
      let kn_map = map toKnEntry kn_givens
      -- Try to solve the wanted KnownNat constraints given the [G]iven
      -- KnownNat constraints
      (solved,new) <- (unzip . catMaybes) <$> (mapM (constraintToEvTerm defs kn_map) kn_wanteds)
      return (TcPluginOk solved (concat new))

-- | Get the KnownNat constraints
toKnConstraint :: Ct -> Maybe KnConstraint
toKnConstraint ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
  ClassPred cls [ty]
    |  className cls == knownNatClassName
    -> Just (ct,cls,ty)
  _ -> Nothing

-- | Create a look-up entry for @n@ given a [G]iven @KnownNat n@ constraint.
toKnEntry :: KnConstraint -> (CType,EvVar)
toKnEntry (ct,_,ty) = let ct_ev = ctEvidence ct
                          evT   = ctev_evar ct_ev
                      in  (CType ty,evT)

-- | Find the \"magic\" classes and instances in "GHC.TypeLits.KnownNat"
lookupKnownNatDefs :: TcPluginM KnownNatDefs
lookupKnownNatDefs = do
    md     <- lookupModule myModule myPackage
    kn2C   <- look md "KnownNat2"
    return $ KnownNatDefs kn2C
  where
    look md s = do
      nm   <- lookupName md (mkTcOcc s)
      tcLookupClass nm

    myModule  = mkModuleName "GHC.TypeLits.KnownNat"
    myPackage = fsLit "ghc-typelits-knownnat"

-- | Try to create evidence for a wanted constraint
constraintToEvTerm :: KnownNatDefs -> [(CType,EvVar)] -> KnConstraint
                   -> TcPluginM (Maybe ((EvTerm,Ct),[Ct]))
constraintToEvTerm defs kn_map (ct,cls,op) = (fmap (first (,ct))) <$> go op
  where
    go :: Type -> TcPluginM (Maybe (EvTerm,[Ct]))
    go ty@(LitTy (NumTyLit i)) = return ((,[]) <$> makeLitDict cls ty i)
    go ty@(TyConApp tc [x,y])
      | let tcNm = tyConName tc
      , Just m <- nameModule_maybe tcNm
      = do let mS  = moduleNameString (moduleName m)
               tcS = occNameString (nameOccName tcNm)
               fn  = mkStrLitTy (fsLit (mS ++ "." ++ tcS))
           ienv <- getInstEnvs
           case lookupUniqueInstEnv ienv (kn2 defs) [fn,mkNumLitTy 0,mkNumLitTy 0] of
             Right (inst, _) -> runMaybeT $ do
               (xEv,newX) <- MaybeT (go x)
               (yEv,newY) <- MaybeT (go y)
               let df = (kn2 defs,instanceDFunId inst)
               (MaybeT . return) ((,newX ++ newY) <$> makeOpDict df cls fn x y ty xEv yEv)
             _ -> return ((,[]) <$> (EvId <$> lookup (CType ty) kn_map))
    go ty = return ((,[]) <$> (EvId <$> lookup (CType ty) kn_map))

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
           -> Type           -- ^ Symbol representing the function
           -> Type           -- ^ Type of the first argument
           -> Type           -- ^ Type of the second argument
           -> Type           -- ^ Type of the result
           -> EvTerm         -- ^ KnownNat dictionary for the first argument
           -> EvTerm         -- ^ KnownNat dictionary for the second argument
           -> Maybe EvTerm
makeOpDict (opCls,dfid) knCls f x y z xEv yEv
  | Just (_, kn_co_dict) <- tcInstNewTyCon_maybe (classTyCon knCls) [z]
    -- KnownNat n ~ SNat n
  , [ kn_meth ] <- classMethods knCls
  , Just kn_tcRep <- tyConAppTyCon_maybe -- SNat
                      $ funResultTy      -- SNat n
                      $ dropForAlls      -- KnownNat n => SNat n
                      $ idType kn_meth   -- forall n. KnownNat n => SNat n
  , Just (_, kn_co_rep) <- tcInstNewTyCon_maybe kn_tcRep [z]
    -- SNat n ~ Integer
  , Just (_, op_co_dict) <- tcInstNewTyCon_maybe (classTyCon opCls) [f,x,y]
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
