{-# LANGUAGE DataKinds, ScopedTypeVariables, TypeOperators, TypeApplications, FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, TypeFamilies, TypeInType, UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Test where

import Data.Proxy
import GHC.TypeLits
import Test.Tasty
import Test.Tasty.HUnit

import GHC.TypeLits.KnownNat
import Data.Singletons         (Apply, type (~>))
import Data.Singletons.Prelude (If)

type family Max (a :: Nat) (b :: Nat) :: Nat where
  Max 0 b = b -- See [Note: single equation TFs are treated like synonyms]
  Max a b = If (a <=? b) b a

data MaxSym1 :: Nat -> Nat ~> Nat
data MaxSym2 :: Nat ~> Nat ~> Nat

type instance Apply MaxSym2 a     = (MaxSym1 a)
type instance Apply (MaxSym1 a) b = Max a b

instance (KnownNat a, KnownNat b) => KnownNat2 "Test.Max" a b where
  type KnownNatF2 "Test.Max" = MaxSym2
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

test1 :: forall n . KnownNat n => Proxy n -> Integer
test1 _ = natVal (Proxy :: Proxy n) + natVal (Proxy :: Proxy (n+2))

test2 :: forall n . KnownNat n => Proxy n -> Integer
test2 _ = natVal (Proxy :: Proxy (n*3))

test3 :: forall n m . (KnownNat n, KnownNat m) => Proxy n -> Proxy m -> Integer
test3 _ _ = natVal (Proxy :: Proxy (n+m))

test4 :: forall n m . (KnownNat n, KnownNat m) => Proxy n -> Proxy m -> Integer
test4 _ _ = natVal (Proxy :: Proxy (n*m))

test5 :: forall n m . (KnownNat n, KnownNat m) => Proxy n -> Proxy m -> Integer
test5 _ _ = natVal (Proxy :: Proxy (n^m))

test6 :: forall n m . (KnownNat n, KnownNat m) => Proxy n -> Proxy m -> Integer
test6 _ _ = natVal (Proxy :: Proxy ((n^m)+(n*m)))

test7 :: forall n m . (KnownNat m, KnownNat n) => Proxy n -> Proxy m -> Integer
test7 _ _ = natVal (Proxy :: Proxy (Max n m + 1))

test8 :: forall n m . (KnownNat (Min n m)) => Proxy n -> Proxy m -> Integer
test8 _ _ = natVal (Proxy :: Proxy (Min n m + 1))

test9 :: forall n m . (KnownNat m, KnownNat n, n <= m) => Proxy m -> Proxy n -> Integer
test9 _ _ = natVal (Proxy :: Proxy (m-n))

test11 :: forall m . (KnownNat m) => Proxy m -> Integer
test11 _ = natVal (Proxy @ (m*m))

tests :: TestTree
tests = testGroup "ghc-typelits-natnormalise"
  [ testGroup "Basic functionality"
    [ testCase "KnownNat 4 + KnownNat 6 ~ 10" $
      show (test1 (Proxy @ 4)) @?=
      "10"
    , testCase "KnownNat 4 * KnownNat 3 ~ 12" $
      show (test2 (Proxy @ 4)) @?=
      "12"
    , testCase "KnownNat 2 + KnownNat 7 ~ 9" $
      show (test3 (Proxy @ 2) (Proxy @ 7)) @?=
      "9"
    , testCase "KnownNat 2 * KnownNat 7 ~ 14" $
      show (test4 (Proxy @ 2) (Proxy @ 7)) @?=
      "14"
    , testCase "KnownNat 2 ^ KnownNat 7 ~ 128" $
      show (test5 (Proxy @ 2) (Proxy @ 7)) @?=
      "128"
    , testCase "KnownNat 3 ^ KnownNat 7 ~ 2187" $
      show (test5 (Proxy @ 3) (Proxy @ 7)) @?=
      "2187"
    , testCase "(KnownNat 2 ^ KnownNat 7) + (KnownNat 2 * KnownNat 7) ~ 142" $
      show (test6 (Proxy @ 2) (Proxy @ 7)) @?=
      "142"
    , testCase "KnownNat (Max 7 5 + 1) ~ 8" $
      show (test7 (Proxy @ 7) (Proxy @ 5)) @?=
      "8"
    , testCase "KnownNat (Min 7 5 + 1) ~ 6" $
      show (test8 (Proxy @ 7) (Proxy @ 5)) @?=
      "6"
    , testCase "KnownNat (7 - 5) ~ 2" $
      show (test9 (Proxy @ 7) (Proxy @ 5)) @?=
      "2"
    ],
    testGroup "Implications"
    [ testCase "KnownNat m => KnownNat (m*m); @ 5" $
      show (test11 (Proxy @ 5)) @?=
      "25"
    ]
  ]

main :: IO ()
main = defaultMain tests
