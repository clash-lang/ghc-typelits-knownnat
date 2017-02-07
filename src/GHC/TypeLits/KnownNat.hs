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
import Data.Singletons.TH    (genDefunSymbols)
import GHC.TypeLits.KnownNat

$(genDefunSymbols [''Max]) -- creates the \'MaxSym0\' symbol

instance (KnownNat a, KnownNat b) => 'KnownNat2' $('nameToSymbol' ''Max) a b where
  type 'KnownNatF2' $('nameToSymbol' ''Max) = MaxSym0
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
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE UndecidableInstances  #-}

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
import GHC.TypeLits           (KnownNat, Nat, Symbol, type (+), type (*),
                               type (^), type (-), type (<=), natVal)
import Data.Singletons        (type (~>), type (@@))
import Data.Promotion.Prelude (type (:+$), type (:*$), type (:^$), type (:-$))

import GHC.TypeLits.KnownNat.TH

-- | Singleton natural number (represented by an integer)
newtype SNatKn (n :: Nat) = SNatKn Integer

-- | Class for arithmetic functions with /one/ argument.
--
-- The 'Symbol' /f/ must correspond to the fully qualified name of the
-- type-level operation. Use 'nameToSymbol' to get the fully qualified
-- TH Name as a 'Symbol'
class KnownNat1 (f :: Symbol) (a :: Nat) where
  type KnownNatF1 f :: Nat ~> Nat
  natSing1 :: SNatKn (KnownNatF1 f @@ a)

-- | Class for arithmetic functions with /two/ arguments.
--
-- The 'Symbol' /f/ must correspond to the fully qualified name of the
-- type-level operation. Use 'nameToSymbol' to get the fully qualified
-- TH Name as a 'Symbol'
class KnownNat2 (f :: Symbol) (a :: Nat) (b :: Nat) where
  type KnownNatF2 f :: Nat ~> Nat ~> Nat
  natSing2 :: SNatKn (KnownNatF2 f @@ a @@ b)

-- | Class for arithmetic functions with /three/ arguments.
--
-- The 'Symbol' /f/ must correspond to the fully qualified name of the
-- type-level operation. Use 'nameToSymbol' to get the fully qualified
-- TH Name as a 'Symbol'
class KnownNat3 (f :: Symbol) (a :: Nat) (b :: Nat) (c :: Nat) where
  type KnownNatF3 f :: Nat ~> Nat ~> Nat ~> Nat
  natSing3 :: SNatKn (KnownNatF3 f @@ a @@ b @@ c)

-- | 'KnownNat2' instance for "GHC.TypeLits"' 'GHC.TypeLits.+'
instance (KnownNat a, KnownNat b) => KnownNat2 $(nameToSymbol ''(+)) a b where
  type KnownNatF2 $(nameToSymbol ''(+)) = (:+$)
  natSing2 = SNatKn (natVal (Proxy @a) + natVal (Proxy @b))
  {-# INLINE natSing2 #-}

-- | 'KnownNat2' instance for "GHC.TypeLits"' 'GHC.TypeLits.*'
instance (KnownNat a, KnownNat b) => KnownNat2 $(nameToSymbol ''(*)) a b where
  type KnownNatF2 $(nameToSymbol ''(*)) = (:*$)
  natSing2 = SNatKn (natVal (Proxy @a) * natVal (Proxy @b))
  {-# INLINE natSing2 #-}

-- | 'KnownNat2' instance for "GHC.TypeLits"' 'GHC.TypeLits.^'
instance (KnownNat a, KnownNat b) => KnownNat2 $(nameToSymbol ''(^)) a b where
  type KnownNatF2 $(nameToSymbol ''(^)) = (:^$)
  natSing2 = let x = natVal (Proxy @ a)
                 y = natVal (Proxy @ b)
                 z = case x of
                       2 -> shiftL 1 (fromInteger y)
                       _ -> x ^ y
             in  SNatKn z
  {-# INLINE natSing2 #-}

-- | 'KnownNat2' instance for "GHC.TypeLits"' 'GHC.TypeLits.-'
instance (KnownNat a, KnownNat b, b <= a) => KnownNat2 $(nameToSymbol ''(-)) a b where
  type KnownNatF2 $(nameToSymbol ''(-)) = (:-$)
  natSing2 = SNatKn (natVal (Proxy @a) - natVal (Proxy @b))
  {-# INLINE natSing2 #-}
