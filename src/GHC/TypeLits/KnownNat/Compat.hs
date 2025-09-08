{-# LANGUAGE CPP #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module GHC.TypeLits.KnownNat.Compat
  ( KnownNatDefs(..), lookupKnownNatDefs
  , mkNaturalExpr

  , coercionRKind, classMethodTy
  , irrelevantMult
  )
  where

-- base
import Data.Type.Bool
  ( If )
#if MIN_VERSION_ghc(9,1,0)
import Data.Type.Ord
  ( OrdCond )
#else
import GHC.TypeNats
  ( type (<=) )
#endif


-- ghc-tcplugin-api
import GHC.TcPlugin.API
#if MIN_VERSION_ghc(9,3,0)
import GHC.TcPlugin.API.Internal ( unsafeLiftTcM )
#endif

-- ghc
import qualified GHC.Core.Make as GHC
  ( mkNaturalExpr )
#if MIN_VERSION_ghc(9,3,0)
import GHC.Tc.Utils.Monad
  ( getPlatform )
#endif
#if MIN_VERSION_ghc(8,11,0)
import GHC.Core.Coercion
  ( coercionRKind )
import GHC.Core.Predicate
  ( classMethodTy )
import GHC.Core.Type
  ( irrelevantMult )
#else
import GHC.Core.Coercion
  ( coercionKind )
import GHC.Core.Type
  ( dropForAlls, funResultTy, varType )
import GHC.Data.Pair
  ( Pair(..) )
#endif

-- ghc-typelits-knownnat
import GHC.TypeLits.KnownNat
  ( KnownNat1, KnownNat2, KnownNat3
  , KnownBool, KnownBoolNat2, KnownNat2Bool
  )

-- template-haskell
import qualified Language.Haskell.TH as TH
  ( Name )

--------------------------------------------------------------------------------

-- | Classes and instances from "GHC.TypeLits.KnownNat"
data KnownNatDefs
  = KnownNatDefs
  { knownBool     :: Class
  , knownBoolNat2 :: Class
  , knownNat2Bool :: Class
  , knownNatN     :: Int -> Maybe Class -- ^ KnownNat{N}
#if MIN_VERSION_ghc(9,1,0)
  , ordCondTyCon  :: TyCon
#else
    -- | @<= :: Nat -> Nat -> Constraint@
  , leqNatTyCon   :: TyCon
#endif
  , ifTyCon       :: TyCon
  }

-- | Find the \"magic\" classes and instances in "GHC.TypeLits.KnownNat"
lookupKnownNatDefs :: TcPluginM Init KnownNatDefs
lookupKnownNatDefs = do
    kbC    <- look ''KnownBool
    kbn2C  <- look ''KnownBoolNat2
    kn2bC  <- look ''KnownNat2Bool
    kn1C   <- look ''KnownNat1
    kn2C   <- look ''KnownNat2
    kn3C   <- look ''KnownNat3
#if MIN_VERSION_ghc(9,1,0)
    ordcond <- lookupTHName ''OrdCond >>= tcLookupTyCon
#else
    leq     <- lookupTHName ''(<=) >>= tcLookupTyCon
#endif
    ifTc <- lookupTHName ''If >>= tcLookupTyCon
    return KnownNatDefs
           { knownBool     = kbC
           , knownBoolNat2 = kbn2C
           , knownNat2Bool = kn2bC
           , knownNatN     = \case { 1 -> Just kn1C
                                   ; 2 -> Just kn2C
                                   ; 3 -> Just kn3C
                                   ; _ -> Nothing
                                   }
#if MIN_VERSION_ghc(9,1,0)
           , ordCondTyCon  = ordcond
#else
           , leqNatTyCon   = leq
#endif
           , ifTyCon       = ifTc
           }
  where
    look :: TH.Name -> TcPluginM Init Class
    look nm = lookupTHName nm >>= tcLookupClass

--------------------------------------------------------------------------------

mkNaturalExpr :: Integer -> TcPluginM Solve CoreExpr
mkNaturalExpr i = do
#if MIN_VERSION_ghc(9,3,0)
    platform <- unsafeLiftTcM getPlatform
    return $ GHC.mkNaturalExpr platform i
#elif MIN_VERSION_ghc(8,11,0)
    return $ GHC.mkNaturalExpr i
#else
    GHC.mkNaturalExpr i
#endif

--------------------------------------------------------------------------------

#if !MIN_VERSION_ghc(8,11,0)
coercionRKind :: Coercion -> Type
coercionRKind co = rhs
  where
    Pair _ rhs = coercionKind co
#endif

--------------------------------------------------------------------------------

#if !MIN_VERSION_ghc(8,11,0)
classMethodTy :: Id -> Type
classMethodTy sel_id
  = funResultTy $        -- meth_ty
    dropForAlls $        -- C a => meth_ty
    varType sel_id        -- forall a. C n => meth_ty
#endif

--------------------------------------------------------------------------------

#if !MIN_VERSION_ghc(8,11,0)
irrelevantMult :: a -> a
irrelevantMult = id
#endif

--------------------------------------------------------------------------------
