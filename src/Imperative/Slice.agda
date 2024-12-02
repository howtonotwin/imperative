{-# OPTIONS --safe #-}
-- model of references into random access heap memory
module Imperative.Slice where

open import Agda.Primitive
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality renaming (trans to infixl 1 _∙_)

-- a Slice is a reference to a piece of an underlying allocation
-- see Imperative.Impl for how Array (the allocation type constructor) gets its
-- value
-- n is the length of the slice
record Slice (Array : @0 ℕ → Set lzero) (@0 n : ℕ) : Set lzero where
  constructor slice
  field
    @0 {underlyingLength} : ℕ -- must be a field to state the type of underlying
    underlying : Array underlyingLength
    offset : ℕ
    -- proof that covered memory cells actually exist
    @0 .fit : offset + n ≤ underlyingLength
-- Slice values are easy for Agda to compare/unify

-- a Ref refers to a single memory cell
Ref : (@0 ℕ → Set lzero) → Set lzero
Ref Array = Slice Array 1

-- basic operations
module _ {Array : @0 ℕ → Set lzero} where
  -- reference to the whole of an allocation
  fullSlice : {@0 n : ℕ} → Array n → Slice Array n
  fullSlice a = slice a 0 ≤-refl

  -- Python-like notation for subslice of s starting at offset i with length l
  -- (p is a proof that the specified numbers are valid)
  infixl 10 _[_∶+_because_]
  _[_∶+_because_] : {@0 n : ℕ} → Slice Array n → (i : ℕ) (@0 l : ℕ) → @0 .(l + i ≤ n) → Slice Array l
  slice a o fit [ i ∶+ l because p ] =
    let @0 n : _; n = _ in
    slice a (i + o)
      (≤-trans
        (subst (_≤ o + n)
          (cong (o +_) (+-comm l i) ∙ sym (+-assoc o i l) ∙ cong (_+ l) (+-comm o i))
          (+-monoʳ-≤ o p))
        fit)
  -- special case of l = 1 that looks more like normal array indexing
  infixl 10 _[_because_]
  _[_because_] : {@0 n : ℕ} → Slice Array n → (i : ℕ) → @0 .(i < n) → Ref Array
  _[_because_] = _[_∶+ 1 because_]

  -- C-like notation for the first element of a slice (in C, *p = p[0])
  -- quirk: * (* s) ≡ * s
  infixr 9 *_
  *_ : {@0 n : ℕ} → Slice Array (suc n) → Ref Array
  *_ = _[ 0 because z<s ]
  -- C-like notation for the "pointer increment" (tail) of a slice
  -- ++ s of course doesn't modify s
  infixr 9 ++_
  ++_ : {@0 n : ℕ} → Slice Array (suc n) → Slice Array n
  ++_ {n = n} = _[ 1 ∶+ _ because subst (_≤ suc n) (+-comm 1 n) ≤-refl ]

  -- Python-like notation for the last cell of a slice
  infixl 10 _[-1]
  _[-1] : {n : ℕ} → Slice Array (suc n) → Ref Array
  _[-1] {n} = _[ n because n<1+n n ]
  -- and for the all-but-last subslice
  infixl 10 _[∶-1]
  _[∶-1] : {@0 n : ℕ} → Slice Array (suc n) → Slice Array n
  _[∶-1] {n} = _[ 0 ∶+ n because subst (_≤ suc n) (+-comm 0 n) (n≤1+n n) ]

  -- utility for proving equalities in Slice
  eqSlice :
    {n : ℕ} {x y : Slice Array n} (open Slice)
    (e₁ : underlyingLength x ≡ underlyingLength y) (e₂ : subst (λ n → Array n) e₁ (underlying x) ≡ underlying y)
    (e₃ : offset x ≡ offset y) →
    x ≡ y
  eqSlice refl refl refl = refl

  -- rewriting of a Slice's length
  substSlice : {@0 n m : ℕ} → @0 .(n ≡ m) → Slice Array n → Slice Array m
  substSlice e (slice a o p) = slice a o (subst _ e p)
