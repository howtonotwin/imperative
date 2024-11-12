Here we define the `Condition` data type. A `Condition` is a description of the
state of the heap of an imperative program. That is, `Condition` is the type of
*assertions*, a la separation logic: descriptions of what values are contained
in what regions of the mutable memory store (the *heap*). Such assertions form
the pre- and post-conditions of imperative programs.

```
{-# OPTIONS --safe #-}
module Imperative.Condition where
```

<!--
```
open import Agda.Primitive
open import Data.List as List
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.Nat
open import Data.Nat.Properties
open import Data.Unit
open import Relation.Binary.PropositionalEquality renaming (trans to infixl 1 _∙_)

open import ArrayValue
open import Erased
open import LargeEq
open import Realizer

import Imperative.Slice
```
-->

Before we can define what a `Condition` is, we define what an `Assignment` is.
An `Assignment` is simply a piece of data of the form `v ↦ x` where `v` is a
`Ref` (where `Ref` is some type of memory locations or references, here just a
parameter to `Assignment`; see `Imperative` for how this parameter gets a value
in terms of `Imperative.Impl`'s fields), and `x` is a value of any type in a
small `Set` universe.

```
infix 1 _↦_
record Assignment (Ref : Set lzero) : Setω₀ where
  constructor _↦_
  field
    var : Ref
    {contentLevel} : Level
    {contentType} : Set contentLevel
    content : contentType
```

A `Condition` (again, parameterized by a type `Ref` of memory
locations/references) of the program state is then just a list of `Assignment`s
(using the trivial condition `𝟏` as the "nil" and `_⨾_` as the "cons"). (An
actual `List` cannot be used as `Condition` lives in a big universe on account
of being able to contain data from any small universe.) Note that, following in
the style of separation logic, a `Condition` is meant to be interpreted as a
*separate* conjunction of all the contained `Assignment`s. A `Condition` with
two `Assignment`s that have the same `Ref` on the left describes an unreachable
state.

```
infixr 0 _⨾_
data Condition (Ref : Set lzero) : Setω₀ where
  𝟏   : Condition Ref
  _⨾_ : Assignment Ref → Condition Ref → Condition Ref
```

Oftentimes, when writing a `Condition` inside a term, it is not actually
necessary to specify the `content` part of every assignment. The following alias
gives a shorthand for constructing a `Condition` where `v` is "live" but the
value it holds is not explicitly written down (Agda must still be able to infer
it).

```
infixr 0 _⨾⨾_
pattern _⨾⨾_ v r = v ↦ _ ⨾ r
```

Now we can define some operations on `Condition` and prove some properties about
them. Note that since the `Ref` parameter can be inferred when these functions
are used, we generalize over it as an implicit argument.

```
module _ {Ref : Set lzero} where
```

We can extract all the `Ref`s mentioned by a `Condition`.

```
  liveRefs : Condition Ref → List Ref
  liveRefs 𝟏         = []
  liveRefs (x ⨾⨾ xs) = x ∷ liveRefs xs
```

We can take the separate conjunction of two `Condition`s (i.e. append them).

```
  infixr 0 _&_
  _&_ : Condition Ref → Condition Ref → Condition Ref
  𝟏        & ys = ys
  (x ⨾ xs) & ys = x ⨾ xs & ys
```

`liveRefs` distributes over `_&_` and `_&_` is associative.

```
  liveRefs-& : (xs : Condition Ref) (ys : Condition Ref) → liveRefs (xs & ys) ≡ liveRefs xs List.++ liveRefs ys
  liveRefs-& 𝟏         ys = refl
  liveRefs-& (x ⨾⨾ xs) ys = cong (x ∷_) (liveRefs-& xs ys)

  assoc& : (l m r : Condition Ref) → (l & m) & r ≡ω₀ l & m & r
  assoc& 𝟏        m r = reflω₀
  assoc& (v ⨾⨾ l) m r = congω₀ (v ⨾⨾_) (assoc& l m r)
```

Now we specialize to the case where `Ref` is derived from an underlying `Array`
type, as it is in `Imperative.Slice`.

```
module _ {Array : @0 ℕ → Set lzero} where
  open Imperative.Slice
```

Given a slice of an array and an equal-sized table of values (an `ArrayValue` is
essentially a `List` where the elements can have varying types in varying
universes), we can construct a `Condition` saying that the cells of the slice
are filled up with the values, in order.

```
  infix 1 _↦＊_
  _↦＊_ : {@0 n : ℕ} → Slice Array n → ArrayValue n → Condition (Ref Array)
  s ↦＊ []     = 𝟏
  s ↦＊ x ∷ xs = * s ↦ x ⨾ ++ s ↦＊ xs
```

`_↦＊_` can be pushed under `ArrayValue._∷ʳ_`, at least propositionally.

```
  ↦＊-∷ʳ :
    ∀ {n : ℕ} {ℓ} {A : Set ℓ} (snoc : Slice Array (suc n)) (xs : ArrayValue n) (y : A) →
    snoc ↦＊ (xs ArrayValue.∷ʳ y) ≡ω₀ snoc [∶-1] ↦＊ xs & snoc [-1] ↦ y ⨾ 𝟏
  ↦＊-∷ʳ snoc []       y = reflω₀
  ↦＊-∷ʳ snoc (x ∷ xs) y =
    congω₀ (* snoc ↦ x ⨾_)
      (↦＊-∷ʳ (++ snoc) xs y ∙ω₀ congω₀↑ (λ r → ++ snoc [∶-1] ↦＊ xs & r ↦ y ⨾ 𝟏) (eqSlice refl refl (+-suc _ _)))
```

A length rewrite on one side of `_↦＊_` may be moved to the other side.

```
  substSlice-↦＊-cast :
    {n m : ℕ} (e : n ≡ m) (arr : Slice Array n) (xs : ArrayValue m) →
    substSlice e arr ↦＊ xs ≡ω₀ arr ↦＊ ArrayValue.cast (sym e) xs
  substSlice-↦＊-cast {zero}  e arr []       = reflω₀
  substSlice-↦＊-cast {suc n} e arr (x ∷ xs) = congω₀ (* arr ↦ x ⨾_) (substSlice-↦＊-cast (cong pred e) (++ arr) xs)
```

`_↦＊_` also distributes over `_ArrayValue.++_`. The intended way to call this
lemma is to say `let module MySplit = ↦＊-++ n m combined in ?`, after which
`MySplit.left` will be a slice to the first `n` elements of `combined`,
`MySplit.right` will be a slice to the last `m` elements, and `MySplit.eqn` will
give equalities in terms of `left` and `right`. Note that such a line combines
computation and proof: it both computes the result of incrementing `combined` by
`n` (which is `MySplit.right`) and also provides proof data that can be used to
justify using the computed data.

```
  private
    record ↦＊-++-Bundle (n : ℕ) (@0 m : ℕ) (combined : Slice Array (n + m)) : Setω₀ where
      field
        left : Slice Array n
        right : Slice Array m
        @0 eqn :
          (xs : ArrayValue n) (ys : ArrayValue m) →
          combined ↦＊ xs ArrayValue.++ ys ≡ω₀ left ↦＊ xs & right ↦＊ ys
    open ↦＊-++-Bundle
    ↦＊-++ : (n : ℕ) (@0 m : ℕ) (combined : Slice Array (n + m)) → ↦＊-++-Bundle n m combined
    ↦＊-++ n       m combined .left  = combined [ 0 ∶+ n because +-monoʳ-≤ n z≤n ]
    ↦＊-++ n       m combined .right = combined [ n ∶+ m because subst (_≤ n + m) (+-comm n m) ≤-refl ]
    ↦＊-++ zero    m combined .eqn   []       ys = reflω₀
    ↦＊-++ (suc n) m combined .eqn   (x ∷ xs) ys =
      let left′ = _ in
      congω₀ (* combined ↦ x ⨾_)
        (    ↦＊-++ n m (++ combined) .eqn xs ys
         ∙ω₀ congω₀↑ (λ s → left′ ↦＊ xs & s ↦＊ ys) (eqSlice refl refl (+-suc n _)))
  module ↦＊-++ (n : ℕ) (@0 m : ℕ) (combined : Slice Array (n + m)) = ↦＊-++-Bundle (↦＊-++ n m combined)
```
