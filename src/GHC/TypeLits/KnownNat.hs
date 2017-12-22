{-|
Copyright  :  (C) 2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

Some \"magic\" classes and instances to get the "GHC.TypeLits.KnownNat.Solver"
type checker plugin working.

= Usage

Let's say you defined a closed type family @Max@:

@
import Data.Type.Bool (If)
import GHC.TypeLits

type family Max (a :: Nat) (b :: Nat) :: Nat where
  Max 0 b = b
  Max a b = If (a <=? b) b a
@

if you then want the "GHC.TypeLits.KnownNat.Solver" to solve 'KnownNat'
constraints over @Max@, given just 'KnownNat' constraints for the arguments
of @Max@, then you must define:

@
\{\-# LANGUAGE DataKinds, FlexibleInstances, GADTs, KindSignatures,
             MultiParamTypeClasses, ScopedTypeVariables, TemplateHaskell,
             TypeApplications, TypeFamilies, TypeOperators,
             UndecidableInstances \#-\}

import Data.Proxy            (Proxy (..))
import GHC.TypeLits.KnownNat

instance (KnownNat a, KnownNat b) => 'KnownNat2' $('nameToSymbol' ''Max) a b where
  natSing2 = let x = natVal (Proxy @a)
                 y = natVal (Proxy @b)
                 z = max x y
             in  'SNatKn' z
  \{\-# INLINE natSing2 \#-\}
@

= FAQ

==== 1. "GHC.TypeLits.KnownNat.Solver" does not seem to find the corresponding 'KnownNat2' instance for my type-level operation
At the Core-level, GHCs internal mini-Haskell, type families that only have a
single equation are treated like type synonyms.

For example, let's say we defined a closed type family @Max@:

@
import Data.Type.Bool (If)
import GHC.TypeLits

type family Max (a :: Nat) (b :: Nat) :: Nat where
  Max a b = If (a <=? b) b a
@

Now, a Haskell-level program might contain a constraint

@
KnownNat (Max a b)
@

, however, at the Core-level, this constraint is expanded to:

@
KnownNat (If (a <=? b) b a)
@

"GHC.TypeLits.KnownNat.Solver" never sees any reference to the @Max@ type
family, so it will not look for the corresponding 'KnownNat2' instance either.
To fix this, ensure that your type-level operations always have at
least two equations. For @Max@ this means we have to redefine it as:

@
type family Max (a :: Nat) (b :: Nat) :: Nat where
  Max 0 b = b
  Max a b = If (a <=? b) b a
@
-}

{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}

{-# LANGUAGE Trustworthy #-}

{-# OPTIONS_GHC -Wno-unused-top-binds -fexpose-all-unfoldings #-}
{-# OPTIONS_HADDOCK show-extensions #-}

module GHC.TypeLits.KnownNat
  ( -- * Singleton natural number
    SNatKn (..)
    -- * Constraint-level arithmetic classes
  , KnownNat1 (..)
  , KnownNat2 (..)
  , KnownNat3 (..)
    -- * Template Haskell helper
  , nameToSymbol
  )
where

import Data.Bits              (shiftL)
import Data.Proxy             (Proxy (..))
#if MIN_VERSION_ghc(8,2,0)
import GHC.TypeNats
  (KnownNat, Nat, type (+), type (*), type (^), type (-), type (<=), natVal)
import GHC.TypeLits           (Symbol)
import Numeric.Natural        (Natural)
#else
import GHC.TypeLits           (KnownNat, Nat, Symbol, type (+), type (*),
                               type (^), type (-), type (<=), natVal)
#endif

import GHC.TypeLits.KnownNat.TH

-- | Singleton natural number
newtype SNatKn (f :: Symbol) =
#if MIN_VERSION_ghc(8,2,0)
  SNatKn Natural
#else
  SNatKn Integer
#endif

-- | Class for arithmetic functions with /one/ argument.
--
-- The 'Symbol' /f/ must correspond to the fully qualified name of the
-- type-level operation. Use 'nameToSymbol' to get the fully qualified
-- TH Name as a 'Symbol'
class KnownNat1 (f :: Symbol) (a :: Nat) where
  natSing1 :: SNatKn f

-- | Class for arithmetic functions with /two/ arguments.
--
-- The 'Symbol' /f/ must correspond to the fully qualified name of the
-- type-level operation. Use 'nameToSymbol' to get the fully qualified
-- TH Name as a 'Symbol'
class KnownNat2 (f :: Symbol) (a :: Nat) (b :: Nat) where
  natSing2 :: SNatKn f

-- | Class for arithmetic functions with /three/ arguments.
--
-- The 'Symbol' /f/ must correspond to the fully qualified name of the
-- type-level operation. Use 'nameToSymbol' to get the fully qualified
-- TH Name as a 'Symbol'
class KnownNat3 (f :: Symbol) (a :: Nat) (b :: Nat) (c :: Nat) where
  natSing3 :: SNatKn f

-- | 'KnownNat2' instance for "GHC.TypeLits"' 'GHC.TypeLits.+'
instance (KnownNat a, KnownNat b) => KnownNat2 $(nameToSymbol ''(+)) a b where
  natSing2 = SNatKn (natVal (Proxy @a) + natVal (Proxy @b))
  {-# INLINE natSing2 #-}

-- | 'KnownNat2' instance for "GHC.TypeLits"' 'GHC.TypeLits.*'
instance (KnownNat a, KnownNat b) => KnownNat2 $(nameToSymbol ''(*)) a b where
  natSing2 = SNatKn (natVal (Proxy @a) * natVal (Proxy @b))
  {-# INLINE natSing2 #-}

-- | 'KnownNat2' instance for "GHC.TypeLits"' 'GHC.TypeLits.^'
instance (KnownNat a, KnownNat b) => KnownNat2 $(nameToSymbol ''(^)) a b where
  natSing2 = let x = natVal (Proxy @ a)
                 y = natVal (Proxy @ b)
                 z = case x of
                       2 -> shiftL 1 (fromIntegral y)
                       _ -> x ^ y
             in  SNatKn z
  {-# INLINE natSing2 #-}

-- | 'KnownNat2' instance for "GHC.TypeLits"' 'GHC.TypeLits.-'
instance (KnownNat a, KnownNat b, b <= a) => KnownNat2 $(nameToSymbol ''(-)) a b where
  natSing2 = SNatKn (natVal (Proxy @a) - natVal (Proxy @b))
  {-# INLINE natSing2 #-}
