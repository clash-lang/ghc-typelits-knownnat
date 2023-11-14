# Changelog for the [`ghc-typelits-knownnat`](http://hackage.haskell.org/package/ghc-typelits-knownnat) package

## 0.7.10 *November 14th 2023*
* Work around [GHC issue 23109](https://gitlab.haskell.org/ghc/ghc/-/issues/23109)

## 0.7.9 *October 10th 2023*
* Support for GHC 9.8.1

## 0.7.8 *February 20th 2023*
* Support for GHC-9.6.0.20230210

## 0.7.7 *October 10th 2022*
* Add support for GHC 9.4

## 0.7.6 *June 18th 2021*
* Add support for GHC 9.2.0.20210422

## 0.7.5 *February 10th 2021*
* Raise upper limit for TH dep to allow building on ghc-9.0.1

## 0.7.4 *January 1st 2021*
* Add support for GHC 9.0.1-rc1

## 0.7.3 *July 25th 2020*
* Fix https://github.com/clash-lang/clash-compiler/issues/1454

## 0.7.2 *February 6th 2020*
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
