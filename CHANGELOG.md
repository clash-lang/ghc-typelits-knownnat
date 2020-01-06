# Changelog for the [`ghc-typelits-knownnat`](http://hackage.haskell.org/package/ghc-typelits-knownnat) package

## 0.7.2
 * Add support for GHC 8.10.0-alpha2

## 0.7.1 *October 8th 2019*
* Fix [#29](https://github.com/clash-lang/ghc-typelits-knownnat/issues/29)
* Fix [#30](https://github.com/clash-lang/ghc-typelits-knownnat/issues/30)

## 0.7 *August 26th 2018*
* Solve "known" type-level Booleans, also inside `If` (GHC 8.6+)

## 0.6 *September 14th 2018*
* Move `KnownNat2` instances for `Div` and `Mod` from `ghc-typelits-extra` to `ghc-typelits-knownnat`

## 0.5 *May 9th 2018*
* Fix Inferred constraint is too strong [#19](https://github.com/clash-lang/ghc-typelits-knownnat/issues/19)

## 0.4.2 *April 15th 2018*
* Add support for GHC 8.5.20180306

## 0.4.1 *March 17th, 2018*
* Add support for GHC 8.4.1

## 0.4 *January 4th, 2018*
* Add partial GHC 8.4.1-alpha1 support
* Drop `singletons` dependency [#15](https://github.com/clash-lang/ghc-typelits-knownnat/issues/15)
  * `KnownNatN` classes no longer have the `KnownNatFN` associated type family

## 0.3.1 *August 17th 2017*
* Fix testsuite for GHC 8.2.1

## 0.3 *May 15th 2017*
* GHC 8.2.1 support: Underlying representation for `KnownNat` in GHC 8.2 is `Natural`, meaning users of this plugin will need to update their code to use `Natural` for GHC 8.2 as well.

## 0.2.4 *April 10th 2017*
* New features:
  * Derive constraints for unary functions via a `KnownNat1` instance; thanks to @nshepperd [#11](https://github.com/clash-lang/ghc-typelits-knownnat/pull/11)
  * Use type-substituted [G]iven KnownNats (partial solve for [#13](https://github.com/clash-lang/ghc-typelits-knownnat/issues/13))

## 0.2.3 *January 15th 2017*
* Solve normalised literal constraints, i.e.:
  * `KnownNat (((addrSize + 1) - (addrSize - 1))) ~ KnownNat 2`

## 0.2.2 *September 29th 2016*
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
