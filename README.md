# ghc-typelits-knownnat

[![Build Status](https://github.com/clash-lang/ghc-typelits-knownnat/actions/workflows/haskell-ci.yml/badge.svg?branch=master)](https://github.com/clash-lang/ghc-typelits-knownnat/actions)
[![Hackage](https://img.shields.io/hackage/v/ghc-typelits-knownnat.svg)](https://hackage.haskell.org/package/ghc-typelits-knownnat)
[![Hackage Dependencies](https://img.shields.io/hackage-deps/v/ghc-typelits-knownnat.svg?style=flat)](http://packdeps.haskellers.com/feed?needle=exact%3Aghc-typelits-knownnat)

A type checker plugin for GHC that can derive "complex" `KnownNat`
constraints from other simple/variable `KnownNat` constraints. i.e. without this
plugin, you must have both a `KnownNat n` and a `KnownNat (n+2)` constraint in
the type signature of the following function:

```haskell
f :: forall n . (KnownNat n, KnownNat (n+2)) => Proxy n -> Integer
f _ = natVal (Proxy :: Proxy n) + natVal (Proxy :: Proxy (n+2))
```

Using the plugin you can omit the `KnownNat (n+2)` constraint:

```haskell
f :: forall n . KnownNat n => Proxy n -> Integer
f _ = natVal (Proxy :: Proxy n) + natVal (Proxy :: Proxy (n+2))
```

The plugin can derive `KnownNat` constraints for types consisting of:

* Type variables, when there is a corresponding `KnownNat` constraint
* Type-level naturals
* Applications of the arithmetic expression: `{+,-,*,^}`
* Type functions, when there is either:
  * a matching given `KnownNat` constraint; or
  * a corresponding `KnownNat<N>` instance for the type function

To elaborate the latter points, given the type family `Min`:

```haskell
type family Min (a :: Nat) (b :: Nat) :: Nat where
  Min 0 b = 0
  Min a b = If (a <=? b) a b
```

the plugin can derive a `KnownNat (Min x y + 1)` constraint given only a
`KnownNat (Min x y)` constraint:

```haskell
g :: forall x y . (KnownNat (Min x y)) => Proxy x -> Proxy y -> Integer
g _ _ = natVal (Proxy :: Proxy (Min x y + 1))
```

And, given the type family `Max`:

```haskell
type family Max (a :: Nat) (b :: Nat) :: Nat where
  Max 0 b = b
  Max a b = If (a <=? b) b a
```

and corresponding `KnownNat2` instance:

```haskell
instance (KnownNat a, KnownNat b) => KnownNat2 "TestFunctions.Max" a b where
  natSing2 = let x = natVal (Proxy @a)
                 y = natVal (Proxy @b)
                 z = max x y
             in  SNatKn z
  {-# INLINE natSing2 #-}
```

the plugin can derive a `KnownNat (Max x y + 1)` constraint given only a
`KnownNat x` and `KnownNat y` constraint:

```haskell
h :: forall x y . (KnownNat x, KnownNat y) => Proxy x -> Proxy y -> Integer
h _ _ = natVal (Proxy :: Proxy (Max x y + 1))
```

To use the plugin, add the

```
OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver
```

Pragma to the header of your file.
