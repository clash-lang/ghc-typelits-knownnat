{-|
Copyright  :  (C) 2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# OPTIONS_GHC -Wno-unused-imports #-}

module GHC.TypeLits.KnownNat.TH where

import GHC.TypeLits        (Symbol) -- haddock only
import Language.Haskell.TH (Name, TypeQ, litT, strTyLit)

-- | Convert a TH 'Name' to a type-level 'Symbol'
nameToSymbol :: Name -> TypeQ
nameToSymbol = litT . strTyLit . show
