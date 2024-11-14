Here we define the ways in which an imperative program can divide its heap among
a part that it will allow a subprogram to access and a part that it will keep to
the side and preserve across the call. That is, we define the possible ways the
*frame rule* may be used.

Note that there is actually a very simple definition: if a heap description can
be written as a separate conjunction `pre & side`, then a subprogram with
precondition `pre` and postcondition `post` can run and will result in the
postcondition `post & side`. This is exactly the definition used when giving the
type signature of `frame` in `Imperative.Impl`. However, while this definition
is very simple, it is annoying to actually use, since the work of reordering the
heap description into such a form must be done separately. Thus we develop a
more sophisticated version of `frame` that is reducible to the simple `frame`
but both more convenient to use and amenable to automation.

```
{-# OPTIONS --safe #-}
module Imperative.Framing where
```

<!--
```
open import Agda.Primitive
open import Data.Nat

open import LargeEq
```
-->

We need to talk about heap descriptions as well as ways to reorder and discard
pieces of them.

```
open import Imperative.Condition
open import Imperative.Restructuring
```

We'll abstract over what the memory references actually are.

```
module _ {Ref : Set lzero} where
```

The core definition is the type `Framing`. A `Framing i o d` exists exactly when
`o` forms a subpart of `i` (possibly in a different order), and `d` is the
remainder of `i` (in the same order as it appears in `i`). We can reuse the
(relatively simple) definition of `Restructuring` to define `Framing` just by
adding an index corresponding to `discards`.

```
  data Framing (outer inner : Condition Ref) : Condition Ref → Setω₀ where
    focus : (p : Restructuring outer inner) → Framing outer inner (discards p)
  unfocus : {o i d : Condition Ref} → Framing o i d → Restructuring o i
  unfocus (focus p) = p
```

We can lift the constructors of `Restructuring` to "constructors" of `Framing`.
Note the convention of putting arrows (`<` and `>`) in these names. The arrows
are supposed to point at the part of the `Condition` that is being "focused"
(that is, pieces that are being taken from the "input" `i` of `Framing i o d` to
the "output" `o`). `>[_]╳<` focuses on "nothing" (`𝟏`; note the `╳`!),
`>[_]&[_]⨾[_]⨾⨾>_` focuses on both the one `Ref` it selects and whatever is
selected to the right.

```
  >[_]╳< : (d : Condition Ref) → Framing d 𝟏 d
  >[ d ]╳< = focus [ d ]╳

  infixr -1 >[_]&[_]⨾[_]⨾⨾>_
  >[_]&[_]⨾[_]⨾⨾>_ :
    ∀ (l : Condition Ref)
    (v : Ref) {ℓ} {A : Set ℓ} {x : A}
    (r : Condition Ref) {f d : Condition Ref} →
    Framing (l & r) f d →
    Framing (l & v ↦ x ⨾ r) (v ↦ x ⨾ f) d
  >[ l ]&[ v ]⨾[ r ]⨾⨾> focus p = focus ([ l ]&[ v ]⨾[ r ]⨾⨾ p)
```

We can of course also rewrite the input to `Framing`.

```
  substFraming : {o₁ o₂ i d : Condition Ref} → o₁ ≡ω₀ o₂ → Framing o₁ i d → Framing o₂ i d
  substFraming reflω₀ p = p
```

So far, the rules for `Framing` are not particularly useful, showing no
improvement over `Restructuring`. Specifically, `discards` already computes on
`[_]╳` and `[_]&[_]⨾[_]⨾⨾_`. However, we can also get `Framing`s that select
whole `Condition`s from the input to the output, like `[_]&[_]&[_]⨾⨾_`, _and_
judgementally keep track of the discards. Note that for `Restructuring`,
evaluation of `discards` may get stuck on `[_]&[_]&[_]⨾⨾_`.

```
  infixr 0 _&>_
  _&>_ : {r f d : Condition Ref} (l : Condition Ref) → Framing r f d → Framing (l & r) f (l & d)
  l &> focus [ discards ]╳           = >[ l & discards ]╳<
  l &> focus ([ m ]&[ v ]⨾[ r ]⨾⨾ p) =
      substFraming (assoc& l m (v ⨾⨾ r))
        (>[ l & m ]&[ v ]⨾[ r ]⨾⨾> substFraming (symω₀ (assoc& l m r)) (l &> focus p))
  infixl 0 _<&_
  _<&_ : {l f d : Condition Ref} → Framing l f d → (r : Condition Ref) → Framing (l & r) f (d & r)
  focus [ discards ]╳           <& r = >[ discards & r ]╳<
  focus ([ l ]&[ v ]⨾[ m ]⨾⨾ p) <& r =
    substFraming (symω₀ (assoc& l (v ⨾⨾ m) r))
      (>[ l ]&[ v ]⨾[ m & r ]⨾⨾> substFraming (assoc& l m r) (focus p <& r))
```

Again, the arrows point towards the part of the `Framing` that actually
determines what is selected, while the context is on the other side. We can also
focus a whole `Condition`, discard any condition for `𝟏`, and focus a
`Condition` while rewriting it. (Thus we have the `Framing` versions of `[_]∎`,
`╳`, and `[!_!]∎`).

```
  >[_]< : (cond : Condition Ref) → Framing cond cond 𝟏
  >[ 𝟏         ]< = >[ 𝟏 ]╳<
  >[ v ⨾⨾ cond ]< = >[ 𝟏 ]&[ v ]⨾[ cond ]⨾⨾> >[ cond ]<
  >𝟏< : {cond : Condition Ref} → Framing cond 𝟏 cond
  >𝟏< = >[ _ ]╳<
  >[!_!]< : {pre post : Condition Ref} → pre ≡ω₀ post → Framing pre post 𝟏
  >[! reflω₀ !]< = >[ _ ]<
```

We can also put `Framing`s in sequence, feeding the discards of one into the
input of the next, and taking the conjunction of their outputs.

```
  infixr 1 _<&>_
  _<&>_ :
    {outer first middle second side : Condition Ref} →
    Framing outer first middle → Framing middle second side → Framing outer (first & second) side
  focus [ outer ]╳              <&> q = q
  focus ([ l ]&[ v ]⨾[ r ]⨾⨾ p) <&> q = >[ l ]&[ v ]⨾[ r ]⨾⨾> focus p <&> q
```

The operators `_&>_`, `_<&_`, `>[_]<` and `_<&>_` turn out to be quite useful
for writing `Framing` proofs. Such proofs can be written manually or
automatically (see `Imperative.Solvers`).

Note that while `unfocus` downgrades a `Framing` to a `Restructuring` that
discards its discards, we can also get a `Restructuring` that just puts the
discards aside.

```
  cancelFraming : {o i d : Condition Ref} → Framing o i d → Restructuring o (i & d)
  cancelFraming (focus [ discards ]╳)           = [ discards ]∎
  cancelFraming (focus ([ l ]&[ v ]⨾[ r ]⨾⨾ p)) = [ l ]&[ v ]⨾[ r ]⨾⨾ cancelFraming (focus p)
```
