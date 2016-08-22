# Changelog for the [`ghc-typelits-knownnat`](http://hackage.haskell.org/package/ghc-typelits-knownnat) package

## 0.2.2
* New features:
  * Derive smaller constraints from larger constraints when they differ by a single variable, i.e. `KnownNat (a + b), KnownNat b` implies `KnownNat a`.

## 0.2.1 *August 19th 2016*
* Fixes bugs:
  * Source location of derived wanted constraints is, erroneously, always set to line 1, column 1

## 0.2 *August 17th 2016*
* New features:
  * Handle `GHC.TypeLits.-`
  * Handle custom, user-defined, type-level operations
  * Thanks to Gabor Greif (@ggreif): derive smaller from larger constraints, i.e. `KnownNat (n+1)` implies `KnownNat n`

## 0.1.2
* New features: Solve "complex" KnownNat constraints involving arbitrary type-functions, as long as there is a given KnownNat constraint for this type functions.

## 0.1.1 *August 11th 2016*
* Fixes bug: panic on a non-given KnownNat constraint variable

## 0.1 *August 10th 2016*
* Initial release
