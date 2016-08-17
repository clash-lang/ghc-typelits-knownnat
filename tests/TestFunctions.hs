{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables,
             TypeApplications, TypeFamilies, TypeInType, TypeOperators,
             UndecidableInstances, TemplateHaskell #-}

module TestFunctions where

import Data.Proxy              (Proxy (..))
import Data.Singletons         (Apply, type (~>))
import Data.Type.Bool          (If)
import GHC.TypeLits.KnownNat
import GHC.TypeLits

type family Max (a :: Nat) (b :: Nat) :: Nat where
  Max 0 b = b -- See [Note: single equation TFs are treated like synonyms]
  Max a b = If (a <=? b) b a

data MaxSym1 :: Nat -> Nat ~> Nat
data MaxSym2 :: Nat ~> Nat ~> Nat

type instance Apply MaxSym2 a     = (MaxSym1 a)
type instance Apply (MaxSym1 a) b = Max a b

instance (KnownNat a, KnownNat b) => KnownNat2 $(nameToSymbol ''Max) a b where
  type KnownNatF2 $(nameToSymbol ''Max) = MaxSym2
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
