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
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# LANGUAGE Trustworthy #-}

{-# OPTIONS_GHC -Wno-unused-top-binds -fexpose-all-unfoldings #-}
{-# OPTIONS_HADDOCK show-extensions #-}

module GHC.TypeLits.KnownNat where

import Data.Bits              (shiftL)
import Data.Proxy             (Proxy (..))
import GHC.TypeLits           (KnownNat, Nat, Symbol, natVal)
import Data.Singletons        (type (~>), type (@@))
import Data.Promotion.Prelude (type (:+$), type (:*$), type (:^$))

newtype SNatKn (n :: Nat) = SNatKn Integer

class KnownNat2 (f :: Symbol) (a :: Nat) (b :: Nat) where
  type KnownNatF2 f :: Nat ~> (Nat ~> Nat)
  natSing2 :: SNatKn (KnownNatF2 f @@ a @@ b)

instance (KnownNat a, KnownNat b) => KnownNat2 "GHC.TypeLits.+" a b where
  type KnownNatF2 "GHC.TypeLits.+" = (:+$)
  natSing2 = SNatKn (natVal (Proxy @a) + natVal (Proxy @b))
  {-# INLINE natSing2 #-}

instance (KnownNat a, KnownNat b) => KnownNat2 "GHC.TypeLits.*" a b where
  type KnownNatF2 "GHC.TypeLits.*" = (:*$)
  natSing2 = SNatKn (natVal (Proxy @a) * natVal (Proxy @b))
  {-# INLINE natSing2 #-}

instance (KnownNat a, KnownNat b) => KnownNat2 "GHC.TypeLits.^" a b where
  type KnownNatF2 "GHC.TypeLits.^" = (:^$)
  natSing2 = let x = natVal (Proxy @ a)
                 y = natVal (Proxy @ b)
                 z = case x of
                       2 -> shiftL 1 (fromInteger y)
                       _ -> x ^ y
             in  SNatKn z
  {-# INLINE natSing2 #-}

-- instance (KnownNat a, KnownNat b, b <= a) => KnownNat2 "GHC.TypeLits.-" a b where
--   type KnownNatF2 "GHC.TypeLits.-" = (:-$)
--   natSing2 = SNatKn (natVal (Proxy @a) - natVal (Proxy @b))
--   {-# INLINE natSing2 #-}
