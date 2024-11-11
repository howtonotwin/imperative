{-# OPTIONS --safe #-}
module Imperative.Slice where

open import Agda.Primitive
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality renaming (trans to infixl 1 _∙_)

record Slice (Array : @0 ℕ → Set lzero) (@0 n : ℕ) : Set lzero where
  constructor slice
  field
    @0 {underlyingLength} : ℕ
    underlying : Array underlyingLength
    offset : ℕ
    @0 .fit : offset + n ≤ underlyingLength
Ref : (@0 ℕ → Set lzero) → Set lzero
Ref Array = Slice Array 1
module _ {Array : @0 ℕ → Set lzero} where
  fullSlice : {@0 n : ℕ} → Array n → Slice Array n
  fullSlice a = slice a 0 ≤-refl
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

  infixr 9 *_
  *_ : {@0 n : ℕ} → Slice Array (suc n) → Ref Array
  *_ = _[ 0 because z<s ]
  infixr 9 ++_
  ++_ : {@0 n : ℕ} → Slice Array (suc n) → Slice Array n
  ++_ {n = n} = _[ 1 ∶+ _ because subst (_≤ suc n) (+-comm 1 n) ≤-refl ]

  infixl 10 _[-1] _[∶-1]
  _[-1] : {n : ℕ} → Slice Array (suc n) → Ref Array
  _[-1] {n} = _[ n because n<1+n n ]
  _[∶-1] : {@0 n : ℕ} → Slice Array (suc n) → Slice Array n
  _[∶-1] {n} = _[ 0 ∶+ n because subst (_≤ suc n) (+-comm 0 n) (n≤1+n n) ]

  eqSlice :
    {n : ℕ} {x y : Slice Array n} (open Slice)
    (e₁ : underlyingLength x ≡ underlyingLength y) (e₂ : subst (λ n → Array n) e₁ (underlying x) ≡ underlying y)
    (e₃ : offset x ≡ offset y) →
    x ≡ y
  eqSlice refl refl refl = refl
  substSlice : {@0 n m : ℕ} → @0 .(n ≡ m) → Slice Array n → Slice Array m
  substSlice e (slice a o p) = slice a o (subst _ e p)
