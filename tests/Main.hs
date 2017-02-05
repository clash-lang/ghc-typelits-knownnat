{-# LANGUAGE DataKinds, GADTs, KindSignatures, ScopedTypeVariables, TypeOperators,
             TypeApplications, TypeFamilies, TypeFamilyDependencies, FlexibleContexts #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Main where

import Data.Proxy
import Data.Type.Equality ((:~:)(..))
import GHC.TypeLits
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Unsafe.Coerce (unsafeCoerce)

import TestFunctions

logT :: Integer -> Integer
logT n = withNat n $ \(Proxy :: Proxy n) ->
                           natVal (Proxy :: Proxy (Log n))

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

test12 :: forall m . (KnownNat (m+1)) => Proxy m -> Integer
test12 = natVal

test13 :: forall m . (KnownNat (m+3)) => Proxy m -> Integer
test13 = natVal

test14 :: forall m . (KnownNat (4+m)) => Proxy (7+m) -> Integer
test14 = natVal

type family Foo (m :: Nat) = (result :: Nat) | result -> m
fakeFooEvidence :: 1 :~: Foo 1
fakeFooEvidence = unsafeCoerce Refl

test15 :: KnownNat (4 + Foo 1) => Proxy (Foo 1) -> Proxy (4 + Foo 1) -> Integer
test15 _ _ = natVal (Proxy @ (Foo 1 + 7))

test16 :: KnownNat (4 + Foo 1 + Foo 1) => Proxy (Foo 1) -> Proxy (4 + Foo 1 + Foo 1) -> Integer
test16 _ _ = natVal (Proxy @ (Foo 1 + 7 + Foo 1))

test17 :: KnownNat (4 + 2 * Foo 1 + Foo 1) => Proxy (Foo 1) -> Proxy (4 + 2 * Foo 1 + Foo 1) -> Integer
test17 _ _ = natVal (Proxy @ (2 * Foo 1 + 7 + Foo 1))

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

test18 :: SNat (a+1) -> SNat a -> SNat 1
test18 = subSNat

test19 :: SNat (a+b) -> SNat b -> SNat a
test19 = subSNat

test20 :: forall a . (KnownNat (3 * a - a)) => Proxy a -> Integer
test20 _ = natVal (Proxy @ (2 * a))

test21 :: forall m n . (KnownNat (m+n), KnownNat m) => Proxy (m+n) -> Proxy m -> Integer
test21 _ _ = natVal (Proxy :: Proxy n)

test22 :: forall x y . (KnownNat x, KnownNat y) => Proxy x -> Proxy y -> Integer
test22 _ _ = natVal (Proxy :: Proxy (y*x*y))

test23 :: SNat addrSize -> SNat ((addrSize + 1) - (addrSize - 1))
test23 SNat = SNat

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
    , testCase "KnownNat (y*x*y), x=3 y=4 ~ 48" $
      show (test22 (Proxy @3) (Proxy @4))@?=
      "48"
    ],
    testGroup "Implications"
    [ testCase "KnownNat m => KnownNat (m*m); @ 5" $
      show (test11 (Proxy @ 5)) @?=
      "25"
    , testCase "KnownNat (m+1) => KnownNat m; @ m ~ 5" $
      show (test12 (Proxy @ 5)) @?=
      "5"
    , testCase "KnownNat (m+1) => KnownNat m; @ m ~ 0" $
      show (test12 (Proxy @ 0)) @?=
      "0"
    , testCase "KnownNat (m+3) => KnownNat m; @ m ~ 0" $
      show (test13 (Proxy @ 0)) @?=
      "0"
    , testCase "KnownNat (4+m) => KnownNat (7+m); @ m ~ 1" $
      show (test14 (Proxy @ 8)) @?=
      "8"
    , testCase "KnownNat (4 + Foo 1) => KnownNat (Foo 1 + 7); @ Foo 1 ~ 1" $
      (case fakeFooEvidence of
          Refl -> show $ test15 (Proxy @ (Foo 1)) (Proxy @ (4 + Foo 1))) @?=
      "8"
    , testCase "KnownNat (4 + Foo 1 + Foo 1) => KnownNat (Foo 1 + 7 + Foo 1); @ Foo 1 ~ 1" $
      (case fakeFooEvidence of
          Refl -> show $ test16 (Proxy @ (Foo 1)) (Proxy @ (4 + Foo 1 + Foo 1))) @?=
      "9"
    , testCase "KnownNat (4 + 2 * Foo 1 + Foo 1) => KnownNat (2 * Foo 1 + 7 + Foo 1); @ Foo 1 ~ 1" $
      (case fakeFooEvidence of
          Refl -> show $ test17 (Proxy @ (Foo 1)) (Proxy @ (4 + 2 * Foo 1 + Foo 1))) @?=
      "10"
    , testCase "KnownNat (3 * a - a) => KnownNat (2 * a); @ a ~ 4" $
      show (test20 (Proxy @ 4)) @?=
      "8"
    , testCase "KnownNat (a + b), KnownNat b => KnownNat a; @ (a+b) ~ 8, b ~ 6" $
      show (test21 (Proxy @ 8) (Proxy @ 6)) @?=
      "2"
    ],
    testGroup "Normalisation"
    [ testCase "KnownNat (m-n+n) ~ KnownNat m" $
      show (test10 (Proxy @ 12) (Proxy @8)) @?=
      "12"
    , testCase "SNat (a+1) - SNat a = SNat 1" $
      show (test18 (SNat @ 11) (SNat @10)) @?=
      "1"
    , testCase "SNat (a+b) - SNat b = SNat a" $
      show (test19 (SNat @ 16) (SNat @10)) @?=
      "6"
    , testCase "SNat ((addrSize + 1) - (addrSize - 1)) = SNat 2" $
      show (test23 (SNat @ 8)) @?=
      "2"
    ],
    testGroup "QuickCheck"
    [ testProperty "logT = logInt" $ (\a -> (a > 0) ==> (logT a == logInt a)) ]
  ]

main :: IO ()
main = defaultMain tests
