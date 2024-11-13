Here we define the type of state transformations that an imperative program can
make to its heap without actually doing anything. That is, we define a type for
*structural modifications* of a heap description, allowing the order of
description to changed and allowing pieces of the description to be forgotten.
`Program`s written with the interface defined in `Imperative.Impl` can apply
such modifications at any point in the instruction stream with the `restructure`
operation. Such a call is not meant perform any action at runtime, but is often
necessary to show that the pre-/post-conditions of sub-`Program`s in a sequence
match up.

```
{-# OPTIONS --safe #-}
module Imperative.Restructuring where
```

<!--
```
open import Agda.Primitive
open import Data.Nat
open import Relation.Binary.PropositionalEquality

open import LargeEq
```
-->

The heap descriptions we are considering are `Condition`s, as defined in the
module below.

```
open import Imperative.Condition
```

We generalize over the `Ref` parameter of `Condition`.

```
module _ {Ref : Set lzero} where
```

For `input output : Condition Ref`, a `Restructuring input output` exists if
there is a way to transform `input` into `output` by reordering and potentially
deleting `Assignment`s inside `input`.

```
  infixr -1 [_]&[_]⨾[_]⨾⨾_
  data Restructuring : Condition Ref → Condition Ref → Setω₀ where
```

We can forget about the contents of any amount of memory (as described by
`discards`) freely. Afterwards, we only describe that memory by `𝟏`.

```
    [_]╳ : (discards : Condition Ref) → Restructuring discards 𝟏
```

If we instead want preserve knowledge about live `Ref` `v` from the input to the
output, we can put `v` at the head of the output if we can

1. decompose the input description into `l & v ⨾⨾ r` for some `l`, `r` (thus
   ensuring that `v` is actually live in the input heap)
2. and then restructure the remainder `l & r` of the input into the remainder
   `rest` of the output. (That `v` no longer appears in the input in the
   remainder of the `Restructuring` enforces that live references cannot be
   duplicated.)

```
    [_]&[_]⨾[_]⨾⨾_ :
      ∀ (l : Condition Ref)
      (v : Ref) {ℓ} {A : Set ℓ} {x : A}
      (r : Condition Ref) {rest : Condition Ref} →
      Restructuring (l & r) rest →
      Restructuring (l & v ↦ x ⨾ r) (v ↦ x ⨾ rest)
```

These two rules suffice. In fact, if the input `Condition` contains all distinct
`Ref`s, then, for any possible output `Condition`, there is (basically) only one
way to write a `Restructuring input output`. As an example, say we want to show
`Restructuring (x ↦ 1 ⨾ y ↦ 2 ⨾ z ↦ 3 ⨾ 𝟏) (z ↦ 3 ⨾ x ↦ 1 ⨾ 𝟏)`.

```
  module _ (x y z : Ref) where
    _ : Restructuring (x ↦ 1 ⨾ y ↦ 2 ⨾ z ↦ 3 ⨾ 𝟏) (z ↦ 3 ⨾ x ↦ 1 ⨾ 𝟏)
```

Then we should think in terms of the following steps.

1. First, we want to get `z ↦ 3` into the output. In the input, `z ↦ 3` appears
   with `x ↦ 1 ⨾ y ↦ 2 ⨾ 𝟏` on its left and `𝟏` on its right. Thus we take the
   step `[ x ⨾⨾ y ⨾⨾ 𝟏 ]&[ z ]⨾[ 𝟏 ]⨾⨾_` (note we can let the values for `x` and
   `y` be inferred).
2. Next, we want `x ↦ 1`. The input has been reduced to `x ↦ 1 ⨾ y ↦ 2 ⨾ 𝟏`, so
   we have `𝟏` to the left of `x` and `y ↦ 2 ⨾ 𝟏` to the right. Thus the next
   step is `[ 𝟏 ]&[ x ]⨾[ y ⨾⨾ 𝟏 ]⨾⨾_`.
3. Finally, we want to discard `y ↦ 2 ⨾ 𝟏`. We use `[ y ⨾⨾ 𝟏 ]╳`.

The full proof term is given below.

```
    _ = [ x ⨾⨾ y ⨾⨾ 𝟏 ]&[ z ]⨾[ 𝟏 ]⨾⨾ [ 𝟏 ]&[ x ]⨾[ y ⨾⨾ 𝟏 ]⨾⨾ [ y ⨾⨾ 𝟏 ]╳
```

Note that a `Restructuring` value is essentially a list of the references we
want to be live in the output, in the order we want them in, with each
reference annotated with its location in the (reduced) input.

We can define a shorthand for a `[_]╳` where we let the description of what is
being discarded be inferred.

```
  pattern ╳ = [ _ ]╳
```

We can define another shorthand to indicate we don't want to discard anything.

```
  pattern ∎ = [ 𝟏 ]╳
```

Note that `Restructuring` automatically respects propositional equality. We can
define a modified version of `[_]&[_]⨾[_]⨾⨾_` that rewrites value at the focused
location by a given equality.

```
  infixr -1 [_]&[_]↦[_]⨾[_]⨾⨾_
  [_]&[_]↦[_]⨾[_]⨾⨾_ :
      ∀ (l : Condition Ref)
      (v : Ref) {ℓ} {A : Set ℓ} {x y : A} (e : x ≡ y)
      (r : Condition Ref) {rest : Condition Ref} →
      Restructuring (l & r) rest →
      Restructuring (l & v ↦ x ⨾ r) (v ↦ y ⨾ rest)
  [ l ]&[ v ]↦[ refl ]⨾[ r ]⨾⨾ p = [ l ]&[ v ]⨾[ r ]⨾⨾ p
```

A specialization of the above principle to single references comes in handy.

```
  [_]↦[_]∎ : ∀ (v : Ref) {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → Restructuring (v ↦ x ⨾ 𝟏) (v ↦ y ⨾ 𝟏)
  [_]↦[_]∎ = [ 𝟏 ]&[_]↦[_]⨾[ 𝟏 ]⨾⨾ ∎
```

We can construct `Restructuring`s that change nothing.

```
  [_]∎ : (cond : Condition Ref) → Restructuring cond cond
  [ 𝟏         ]∎ = ∎
  [ v ⨾⨾ cond ]∎ = [ 𝟏 ]&[ v ]⨾[ cond ]⨾⨾ [ cond ]∎
```

And we can also lift equalities of `Condition`s to `Restructuring`s.

```
  [!_!]∎ : {pre post : Condition Ref} → pre ≡ω₀ post → Restructuring pre post
  [! reflω₀ !]∎ = [ _ ]∎
```

We can define a variant of `[_]&[_]⨾[_]⨾⨾_` that allows selecting an entire
`Condition` for keeping at once.

```
  infixr -1 [_]&[_]&[_]⨾⨾_
  [_]&[_]&[_]⨾⨾_ :
    (l m r : Condition Ref) {rest : Condition Ref} →
    Restructuring (l & r) rest →
    Restructuring (l & m & r) (m & rest)
  [ l ]&[ 𝟏      ]&[ r ]⨾⨾ p = p
  [ l ]&[ v ⨾⨾ m ]&[ r ]⨾⨾ p = [ l ]&[ v ]⨾[ m & r ]⨾⨾ [ l ]&[ m ]&[ r ]⨾⨾ p
```

Finally, we can compute what is being discarded by a given `Restructuring`.

```
  discards : {pre post : Condition Ref} → Restructuring pre post → Condition Ref
  discards [ discards ]╳           = discards
  discards ([ l ]&[ v ]⨾[ r ]⨾⨾ p) = discards p
```
