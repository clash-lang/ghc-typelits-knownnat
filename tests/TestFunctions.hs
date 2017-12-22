{-# LANGUAGE CPP, DataKinds, FlexibleInstances, GADTs, KindSignatures,
             MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TemplateHaskell,
             TypeApplications, TypeFamilies, TypeOperators,
             UndecidableInstances #-}

module TestFunctions where

import Data.Proxy            (Proxy (..))
import Data.Type.Bool        (If)
import GHC.TypeLits.KnownNat
#if __GLASGOW_HASKELL__ >= 802
import GHC.TypeNats
import Numeric.Natural
#else
import GHC.TypeLits
#endif

type family Max (a :: Nat) (b :: Nat) :: Nat where
  Max 0 b = b -- See [Note: single equation TFs are treated like synonyms]
  Max a b = If (a <=? b) b a

instance (KnownNat a, KnownNat b) => KnownNat2 $(nameToSymbol ''Max) a b where
  natSing2 = let x = natVal (Proxy @ a)
                 y = natVal (Proxy @ b)
                 z = max x y
             in  SNatKn z
  {-# INLINE natSing2 #-}

{- [Note: single equation TFs are treated like synonyms]
Single equation (closed) type families (TF) are treated like type synonyms, this
means that type-applications of such a TF only shows up in its expanded form.

Consequently, the KnownNat solver plugin does not have a TyCon name to look
up the corresponding instance of the KnownNat2 class.
-}

type family Min (a :: Nat) (b :: Nat) :: Nat where
  Min 0 b = 0 -- See [Note: single equation TFs are treated like synonyms]
  Min a b = If (a <=? b) a b

-- Unary functions.
#if __GLASGOW_HASKELL__ >= 802
withNat :: Natural -> (forall n. (KnownNat n) => Proxy n -> r) -> r
withNat n f = case someNatVal n of
  SomeNat proxy -> f proxy
#else
withNat :: Integer -> (forall n. (KnownNat n) => Proxy n -> r) -> r
withNat n f = case someNatVal n of
               Just (SomeNat proxy) -> f proxy
               Nothing              -> error ("withNat: negative value (" ++ show n ++ ")")
#endif

type family Log (n :: Nat) :: Nat where

#if __GLASGOW_HASKELL__ >= 802
logInt :: Natural -> Natural
#else
logInt :: Integer -> Integer
#endif
logInt 0 = error "log 0"
logInt n = go 0
  where
    go k = case compare (2^k) n of
             LT -> go (k + 1)
             EQ -> k
             GT -> k - 1

instance (KnownNat a) => KnownNat1 $(nameToSymbol ''Log) a where
  natSing1 = let x = natVal (Proxy @ a)
             in SNatKn (logInt x)
