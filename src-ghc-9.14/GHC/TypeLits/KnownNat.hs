{-|
Copyright  :  (C) 2016     , University of Twente,
                  2017-2018, QBayLogic B.V.,
                  2017     , Google Inc.
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
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MagicHash             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
#if MIN_VERSION_ghc(8,6,0)
{-# LANGUAGE NoStarIsType #-}
#endif
#if !MIN_VERSION_ghc(8,2,0)
{-# LANGUAGE BangPatterns #-}
#endif

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
    -- * Singleton boolean
  , SBool (..)
  , boolVal
    -- * KnownBool
  , KnownBool (..)
    -- ** Constraint-level boolean functions
  , SBoolKb (..)
  , KnownNat2Bool (..)
  , KnownBoolNat2 (..)
    -- * Template Haskell helper
  , nameToSymbol
  )
where

import GHC.Natural (shiftLNatural)
import Data.Proxy (Proxy (..))
import Data.Type.Bool (If)
import GHC.Prim (Proxy#)
import GHC.TypeNats
  (KnownNat, Nat, type (+), type (*), type (^), type (-), type (<=?), type (<=),
   type Mod, type Div, natVal)
import GHC.TypeLits (Symbol)
import Numeric.Natural (Natural)
import Data.Type.Ord (OrdCond)
import GHC.Types (Constraint)

import GHC.TypeLits.KnownNat.TH

-- | Singleton natural number
newtype SNatKn (f :: Symbol) = SNatKn Natural

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
  {-# NOINLINE natSing2 #-}

-- | 'KnownNat2' instance for "GHC.TypeLits"' 'GHC.TypeLits.*'
instance (KnownNat a, KnownNat b) => KnownNat2 $(nameToSymbol ''(*)) a b where
  natSing2 = SNatKn (natVal (Proxy @a) * natVal (Proxy @b))
  {-# NOINLINE natSing2 #-}

-- | 'KnownNat2' instance for "GHC.TypeLits"' 'GHC.TypeLits.^'
instance (KnownNat a, KnownNat b) => KnownNat2 $(nameToSymbol ''(^)) a b where
  natSing2 = let x = natVal (Proxy @a)
                 y = natVal (Proxy @b)
                 z = case x of
                       2 -> shiftLNatural 1 (fromIntegral y)
                       _ -> x ^ y
             in  SNatKn z
  {-# NOINLINE natSing2 #-}

-- | 'KnownNat2' instance for "GHC.TypeLits"' 'GHC.TypeLits.-'
instance (KnownNat a, KnownNat b, (b <= a) ~ (() :: Constraint)) => KnownNat2 $(nameToSymbol ''(-)) a b where
  natSing2 = SNatKn (natVal (Proxy @a) - natVal (Proxy @b))
  {-# NOINLINE natSing2 #-}

instance (KnownNat x, KnownNat y, (1 <= y) ~ (() :: Constraint)) => KnownNat2 $(nameToSymbol ''Div) x y where
  natSing2 = SNatKn (quot (natVal (Proxy @x)) (natVal (Proxy @y)))
  {-# NOINLINE natSing2 #-}

instance (KnownNat x, KnownNat y, (1 <= y) ~ (() :: Constraint)) => KnownNat2 $(nameToSymbol ''Mod) x y where
  natSing2 = SNatKn (rem (natVal (Proxy @x)) (natVal (Proxy @y)))
  {-# NOINLINE natSing2 #-}

-- | Singleton version of 'Bool'
data SBool (b :: Bool) where
  SFalse :: SBool 'False
  STrue  :: SBool 'True

class KnownBool (b :: Bool) where
  boolSing :: SBool b

instance KnownBool 'False where
  boolSing = SFalse

instance KnownBool 'True where
  boolSing = STrue

-- | Get the 'Bool' value associated with a type-level 'Bool'
--
-- Use 'boolVal' if you want to perform the standard boolean operations on the
-- reified type-level 'Bool'.
--
-- Use 'boolSing' if you need a context in which the type-checker needs the
-- type-level 'Bool' to be either 'True' or 'False'
--
-- @
-- f :: forall proxy b r . KnownBool b => r
-- f = case boolSing @b of
--   SFalse -> -- context with b ~ False
--   STrue  -> -- context with b ~ True
-- @
boolVal :: forall b proxy . KnownBool b => proxy b -> Bool
boolVal _ = case boolSing :: SBool b of
  SFalse -> False
  _      -> True

-- | Get the `Bool` value associated with a type-level `Bool`. See also
-- 'boolVal' and 'Proxy#'.
boolVal' :: forall b . KnownBool b => Proxy# b -> Bool
boolVal' _ = case boolSing :: SBool b of
  SFalse -> False
  _      -> True

-- | A type "representationally equal" to 'SBool', used for simpler
-- implementation of constraint-level functions that need to create instances of
-- 'KnownBool'
newtype SBoolKb (f :: Symbol) = SBoolKb Bool

-- | Class for binary functions with a Boolean result.
--
-- The 'Symbol' /f/ must correspond to the fully qualified name of the
-- type-level operation. Use 'nameToSymbol' to get the fully qualified
-- TH Name as a 'Symbol'
class KnownBoolNat2 (f :: Symbol) (a :: k) (b :: k) where
  boolNatSing2 :: SBoolKb f

instance (KnownNat a, KnownNat b) => KnownBoolNat2 $(nameToSymbol ''(<=?)) a b where
  boolNatSing2 = SBoolKb (natVal (Proxy @a) <= natVal (Proxy @b))
  {-# NOINLINE boolNatSing2 #-}

instance (KnownNat a, KnownNat b) => KnownBoolNat2 $(nameToSymbol ''OrdCond) a b where
  boolNatSing2 = SBoolKb (natVal (Proxy @a) <= natVal (Proxy @b))
  {-# NOINLINE boolNatSing2 #-}

-- | Class for ternary functions with a Natural result.
--
-- The 'Symbol' /f/ must correspond to the fully qualified name of the
-- type-level operation. Use 'nameToSymbol' to get the fully qualified
-- TH Name as a 'Symbol'
class KnownNat2Bool (f :: Symbol) (a :: Bool) (b :: k) (c :: k) where
  natBoolSing3 :: SNatKn f

instance (KnownBool a, KnownNat b, KnownNat c) => KnownNat2Bool $(nameToSymbol ''If) a b c where
  natBoolSing3 = SNatKn (if boolVal (Proxy @a) then natVal (Proxy @b) else natVal (Proxy @c))
  {-# NOINLINE natBoolSing3 #-}
