Here we define `Slice`s and `Ref`s, which are the ways of referring to pieces of
memory in our programming model.

```
{-# OPTIONS --safe #-}
module Imperative.Slice where
```

<!--
```
open import Agda.Primitive
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality renaming (trans to infixl 1 _∙_)
```
-->

A *slice* is a reference to a piece of an allocated array. The type of `Slice`
of slices as defined here is parameterized by the underlying type constructor
for arrays (see `Imperative` for how the value of this parameter is derived from
the fields of `Imperative.Impl`) and indexed by the number of memory cells it
covers.

A `Slice` is a simple record of the underlying allocation together with an
offset. The length `n` of the slice is a part of its type, but, like for arrays
themselves, there is no requirement to know the length of a slice at runtime to
work with it (due to the erasure annotation on `n`). Note that the length of the
underlying array must be a field of `Slice` in order to even state the type of
the `underlying` array, but it can be erased so it doesn't actually need to be
present at runtime. The interpretation is that, when there is a slice, there
*logically* exists a number describing the size of the underlying allocation,
but the slice itself does not contain this information.

```
record Slice (Array : @0 ℕ → Set lzero) (@0 n : ℕ) : Set lzero where
  constructor slice
  field
    @0 {underlyingLength} : ℕ
    underlying : Array underlyingLength
    offset : ℕ
```

`Slice` needs one more field: a *proof* that the memory cells that are claimed
to be accessible actually do exist. Note that this proof is both erased (so it
has no existence at runtime, but is required at compile-time and available for
use in proofs) and irrelevant (marked by the dot) (which means that the specific
*value* of the proof does not logically matter, not even for purposes such as
determining whether two `Slice`s are equal during type-checking).

```
    @0 .fit : offset + n ≤ underlyingLength
```

We can now define some simple notations and operations on slices. First off: a
slice of length 1 constitutes a *reference* to a single memory cell.

```
Ref : (@0 ℕ → Set lzero) → Set lzero
Ref Array = Slice Array 1
```

For the rest of the definitions, which are functions involving `Slice`s, we can
let the `Array` parameter be inferred, and we can use a `module` to succinctly
generalize all the definitions over this parameter.

```
module _ {Array : @0 ℕ → Set lzero} where
```

Given an allocation `a`, there is a slice `fullSlice a` containing all of it.

```
  fullSlice : {@0 n : ℕ} → Array n → Slice Array n
  fullSlice a = slice a 0 ≤-refl
```

Now, starting with a slice `s`, a smaller slice `s [ i ∶+ l because p ]` can be
constructed by specifying an offset `i` and a length `l` (and giving a bounds
proof `p`). The special case of `l = 1` (which produces a `Ref`) is given its
own notation `s [ i because p ]`. (In Agda's syntax, "notations" like these are
actually just calls to functions which have underscores in their names. Custom
`syntax` declarations are also available but not necessary for such simple
cases. The first notation is just a call to `_[_∶+_because_]` and the second a
call to `_[_because_]`.)

```
  infixl 10 _[_because_] _[_∶+_because_]
  _[_∶+_because_] : {@0 n : ℕ} → Slice Array n → (i : ℕ) (@0 l : ℕ) → @0 .(l + i ≤ n) → Slice Array l
  slice a o fit [ i ∶+ l because p ] =
    let @0 n : _; n = _ in
    slice a (i + o)
      (≤-trans
        (subst (_≤ o + n)
          (cong (o +_) (+-comm l i) ∙ sym (+-assoc o i l) ∙ cong (_+ l) (+-comm o i))
          (+-monoʳ-≤ o p))
        fit)
  _[_because_] : {@0 n : ℕ} → Slice Array n → (i : ℕ) → @0 .(i < n) → Ref Array
  _[_because_] = _[_∶+ 1 because_]
```

Note that `_[_because_]` is defined using Agda's generalized section notation,
by supplying just the third argument of `_[_∶+_because_]`.

C-like notations `* s` for the first element of a (nonempty) slice and `++ s`
(that is, the "pointer increment" of `s`) for all but the first element of a
(nonempty) slice are given. (Unlike C, the expression `++ s` of course doesn't
modify `s`! Also a quirk: `* (* s) ≡ * s` always.)

```
  infixr 9 *_ ++_
  *_ : {@0 n : ℕ} → Slice Array (suc n) → Ref Array
  *_ = _[ 0 because z<s ]
  ++_ : {@0 n : ℕ} → Slice Array (suc n) → Slice Array n
  ++_ {n = n} = _[ 1 ∶+ _ because subst (_≤ suc n) (+-comm 1 n) ≤-refl ]
```

Python-like notations for the last cell and all-but-last subslice are also
given. (Yes, to Agda, `_[-1]` and `_[∶-1]` are just identifiers!)

```
  infixl 10 _[-1] _[∶-1]
  _[-1] : {n : ℕ} → Slice Array (suc n) → Ref Array
  _[-1] {n} = _[ n because n<1+n n ]
  _[∶-1] : {@0 n : ℕ} → Slice Array (suc n) → Slice Array n
  _[∶-1] {n} = _[ 0 ∶+ n because subst (_≤ suc n) (+-comm 0 n) (n≤1+n n) ]
```

We can prove two `Slice`s equal by showing that they are equal on corresponding
relevant components. Note that the erased `underlyingLength` fields must be
shown equal, but the irrelevant `fit` fields don't need to be considered.

```
  eqSlice :
    {n : ℕ} {x y : Slice Array n} (open Slice)
    (e₁ : underlyingLength x ≡ underlyingLength y) (e₂ : subst (λ n → Array n) e₁ (underlying x) ≡ underlying y)
    (e₃ : offset x ≡ offset y) →
    x ≡ y
  eqSlice refl refl refl = refl
```

We can also rewrite a `Slice`'s length along an equality.

```
  substSlice : {@0 n m : ℕ} → @0 .(n ≡ m) → Slice Array n → Slice Array m
  substSlice e (slice a o p) = slice a o (subst _ e p)
```
