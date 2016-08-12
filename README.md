# ghc-typelits-knownnat

[![Build Status](https://secure.travis-ci.org/clash-lang/ghc-typelits-knownnat.png?branch=master)](http://travis-ci.org/clash-lang/ghc-typelits-knownnat)
[![Hackage](https://img.shields.io/hackage/v/ghc-typelits-knownnat.svg)](https://hackage.haskell.org/package/ghc-typelits-knownnat)
[![Hackage Dependencies](https://img.shields.io/hackage-deps/v/ghc-typelits-knownnat.svg?style=flat)](http://packdeps.haskellers.com/feed?needle=exact%3Aghc-typelits-knownnat)

A type checker plugin for GHC that can derive "complex" `KnownNat`
constraints from other simple/variable `KnownNat` constraints. i.e. without this
plugin, you must have both a `KnownNat n` and a `KnownNat (n+2)` constraint in
the type signature of the following function:

```
f :: forall n . (KnownNat n, KnownNat (n+2)) => Proxy n -> Integer
f _ = natVal (Proxy :: Proxy n) + natVal (Proxy :: Proxy (n+2))
```

Using the plugin you can omit the `KnownNat (n+2)` constraint:

```
f :: forall n . KnownNat n => Proxy n -> Integer
f _ = natVal (Proxy :: Proxy n) + natVal (Proxy :: Proxy (n+2))
```

The plugin can only derive `KnownNat` constraints consisting of:

* Type-level naturals
* Type variables, when there is a matching given `KnownNat` constraint
* Applications of the arithmetic expression: `{+,*,^}`; i.e. it _cannot_ derive
  a `KnownNat (n-1)` constraint given a `KnownNat n` constraint
* All other types, when there is a matching given `KnownNat` constraint; i.e.
  It _can_ derive a `KnownNat (Max x y + 1)` constraint given a
  `KnownNat (Max x y)` constraint.

To use the plugin, add the

```
OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver
```

Pragma to the header of your file.
