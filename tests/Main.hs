{-# LANGUAGE DataKinds, GADTs, KindSignatures, ScopedTypeVariables, TypeOperators,
             TypeApplications, FlexibleContexts #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Main where

import Data.Proxy
import GHC.TypeLits
import Test.Tasty
import Test.Tasty.HUnit

import TestFunctions

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

test10 :: forall (n :: Nat) m . (KnownNat m) => Proxy m -> Proxy n -> Integer
test10 _ _ = natVal (Proxy :: Proxy (m-n+n))

test11 :: forall m . (KnownNat m) => Proxy m -> Integer
test11 _ = natVal (Proxy @ (m*m))

data SNat :: Nat -> * where
  SNat :: KnownNat n => SNat n

instance Show (SNat n) where
  show s@SNat = show (natVal s)

addSNat :: SNat a -> SNat b -> SNat (a + b)
addSNat SNat SNat = SNat

mulSNat :: SNat a -> SNat b -> SNat (a * b)
mulSNat SNat SNat = SNat

expSNat :: SNat a -> SNat b -> SNat (a ^ b)
expSNat SNat SNat = SNat

subSNat :: (b <= a) => SNat a -> SNat b -> SNat (a - b)
subSNat SNat SNat = SNat

test12 :: SNat (a+1) -> SNat a -> SNat 1
test12 = subSNat

test13 :: SNat (a+b) -> SNat b -> SNat a
test13 = subSNat

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
    ],
    testGroup "Normalisation"
    [ testCase "KnownNat (m-n+n) ~ KnownNat m" $
      show (test10 (Proxy @ 12) (Proxy @8)) @?=
      "12"
    , testCase "SNat (a+1) - SNat a = SNat 1" $
      show (test12 (SNat @ 11) (SNat @10)) @?=
      "1"
    , testCase "SNat (a+b) - SNat b = SNat a" $
      show (test13 (SNat @ 16) (SNat @10)) @?=
      "6"
    ]
  ]

main :: IO ()
main = defaultMain tests
