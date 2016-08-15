{-# LANGUAGE DataKinds, FlexibleContexts, KindSignatures, ScopedTypeVariables
           , TypeOperators, TypeApplications, TypeFamilies, TypeFamilyDependencies #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

import Data.Proxy
import GHC.TypeLits
import Test.Tasty
import Test.Tasty.HUnit
import Data.Type.Equality ((:~:)(..))
import Unsafe.Coerce (unsafeCoerce)

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
    ]
  ]

main :: IO ()
main = defaultMain tests
