{-|
Copyright  :  (C) 2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

Some \"magic\" classes and instances to get the "GHC.TypeLits.KnownNat.Solver"
type checker plugin working.
-}

{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

{-# LANGUAGE Safe #-}

{-# OPTIONS_GHC -Wno-unused-top-binds -fexpose-all-unfoldings #-}
{-# OPTIONS_HADDOCK show-extensions #-}

module GHC.TypeLits.KnownNat () where

import Data.Bits    (shiftL)
import Data.Proxy   (Proxy (..))
import GHC.TypeLits (KnownNat, Nat, type (+), type (*), type (^), natVal)

newtype SNatKn (n :: Nat) = SNatKn Integer

class KnownNatAdd (a :: Nat) (b :: Nat) where
  natSingAdd :: SNatKn (a + b)

instance (KnownNat a, KnownNat b) => KnownNatAdd a b where
  natSingAdd = SNatKn (natVal (Proxy @ a) + natVal (Proxy @ b))
  {-# INLINE natSingAdd #-}

class KnownNatMul (a :: Nat) (b :: Nat) where
  natSingMul :: SNatKn (a * b)

instance (KnownNat a, KnownNat b) => KnownNatMul a b where
  natSingMul = SNatKn (natVal (Proxy @ a) * natVal (Proxy @ b))
  {-# INLINE natSingMul #-}

class KnownNatExp (a :: Nat) (b :: Nat) where
  natSingExp :: SNatKn (a ^ b)

instance (KnownNat a, KnownNat b) => KnownNatExp a b where
  natSingExp = let x = natVal (Proxy @ a)
                   y = natVal (Proxy @ b)
                   z = case x of
                         2 -> shiftL 1 (fromInteger y)
                         _ -> x ^ y
               in  SNatKn z
  {-# INLINE natSingExp #-}
