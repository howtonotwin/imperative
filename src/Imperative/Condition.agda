{-# OPTIONS --safe #-}
open import Agda.Primitive
open import Data.Nat
module Imperative.Condition (StateThread : Setω₀) (Array : StateThread → @0 ℕ → Set lzero) where

open import Data.List as List
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.Nat.Properties
open import Data.Unit
open import Relation.Binary.PropositionalEquality renaming (trans to infixl 1 _∙_)

open import ArrayValue
open import Erased
open import LargeEq
open import Realizer

record Slice (s : StateThread) (@0 n : ℕ) : Set lzero where
  constructor slice
  field
    @0 {underlyingLength} : ℕ
    underlying : Array s underlyingLength
    offset : ℕ
    @0 .fit : offset + n ≤ underlyingLength
Ref : StateThread → Set lzero
Ref s = Slice s 1
module _ {s : StateThread} where
  fullSlice : {@0 n : ℕ} → Array s n → Slice s n
  fullSlice a = slice a 0 ≤-refl
  infixl 10 _[_because_] _[_∶+_because_]
  _[_∶+_because_] : {@0 n : ℕ} → Slice s n → (i : ℕ) (@0 l : ℕ) → @0 .(l + i ≤ n) → Slice s l
  slice a o fit [ i ∶+ l because p ] =
    let @0 n : _; n = _ in
    slice a (i + o)
      (≤-trans
        (subst (_≤ o + n)
          (cong (o +_) (+-comm l i) ∙ sym (+-assoc o i l) ∙ cong (_+ l) (+-comm o i))
          (+-monoʳ-≤ o p))
        fit)
  _[_because_] : {@0 n : ℕ} → Slice s n → (i : ℕ) → @0 .(i < n) → Ref s
  _[_because_] = _[_∶+ 1 because_]

  infixr 9 *_
  *_ : {@0 n : ℕ} → Slice s (suc n) → Ref s
  *_ = _[ 0 because z<s ]
  infixr 9 ++_
  ++_ : {@0 n : ℕ} → Slice s (suc n) → Slice s n
  ++_ {n = n} = _[ 1 ∶+ _ because subst (_≤ suc n) (+-comm 1 n) ≤-refl ]

  infixl 10 _[-1] _[∶-1]
  _[-1] : {n : ℕ} → Slice s (suc n) → Ref s
  _[-1] {n} = _[ n because n<1+n n ]
  _[∶-1] : {@0 n : ℕ} → Slice s (suc n) → Slice s n
  _[∶-1] {n} = _[ 0 ∶+ n because subst (_≤ suc n) (+-comm 0 n) (n≤1+n n) ]

  eqSlice :
    {n : ℕ} {x y : Slice s n} (open Slice)
    (e₁ : underlyingLength x ≡ underlyingLength y) (e₂ : subst (λ n → Array s n) e₁ (underlying x) ≡ underlying y)
    (e₃ : offset x ≡ offset y) →
    x ≡ y
  eqSlice refl refl refl = refl
  substSlice : {@0 n m : ℕ} → @0 .(n ≡ m) → Slice s n → Slice s m
  substSlice e (slice a o p) = slice a o (subst _ e p)

infix 1 _↦_
record Assignment (s : StateThread) : Setω₀ where
  constructor _↦_
  field
    var : Ref s
    {contentLevel} : Level
    {contentType} : Set contentLevel
    content : contentType

infixr 0 _⨾_
data Condition (s : StateThread) : Setω₀ where
  𝟏   : Condition s
  _⨾_ : Assignment s → Condition s → Condition s
infixr 0 _⨾⨾_
pattern _⨾⨾_ v r = v ↦ _ ⨾ r
module _ {s : StateThread} where
  liveRefs : Condition s → List (Ref s)
  liveRefs 𝟏         = []
  liveRefs (x ⨾⨾ xs) = x ∷ liveRefs xs

  infixr 0 _&_
  _&_ : Condition s → Condition s → Condition s
  𝟏        & ys = ys
  (x ⨾ xs) & ys = x ⨾ xs & ys

  infix 1 _↦＊_
  _↦＊_ : {@0 n : ℕ} → Slice s n → ArrayValue n → Condition s
  s ↦＊ []     = 𝟏
  s ↦＊ x ∷ xs = * s ↦ x ⨾ ++ s ↦＊ xs

  liveRefs& : (xs : Condition s) (ys : Condition s) → liveRefs (xs & ys) ≡ liveRefs xs List.++ liveRefs ys
  liveRefs& 𝟏         ys = refl
  liveRefs& (x ⨾⨾ xs) ys = cong (x ∷_) (liveRefs& xs ys)

  assoc& : (l m r : Condition s) → (l & m) & r ≡ω₀ l & m & r
  assoc& 𝟏        m r = reflω₀
  assoc& (v ⨾⨾ l) m r = congω₀ (v ⨾⨾_) (assoc& l m r)

  ↦＊-∷ʳ :
    ∀ {n : ℕ} {ℓ} {A : Set ℓ} (snoc : Slice s (suc n)) (xs : ArrayValue n) (y : A) →
    snoc ↦＊ (xs ArrayValue.∷ʳ y) ≡ω₀ snoc [∶-1] ↦＊ xs & snoc [-1] ↦ y ⨾ 𝟏
  ↦＊-∷ʳ snoc []       y = reflω₀
  ↦＊-∷ʳ snoc (x ∷ xs) y =
    congω₀ (* snoc ↦ x ⨾_)
      (↦＊-∷ʳ (++ snoc) xs y ∙ω₀ congω₀↑ (λ r → ++ snoc [∶-1] ↦＊ xs & r ↦ y ⨾ 𝟏) (eqSlice refl refl (+-suc _ _)))
  substSlice-↦＊-cast :
    {n m : ℕ} (e : n ≡ m) (arr : Slice s n) (xs : ArrayValue m) →
    substSlice e arr ↦＊ xs ≡ω₀ arr ↦＊ ArrayValue.cast (sym e) xs
  substSlice-↦＊-cast {zero}  e arr []       = reflω₀
  substSlice-↦＊-cast {suc n} e arr (x ∷ xs) = congω₀ (* arr ↦ x ⨾_) (substSlice-↦＊-cast (cong pred e) (++ arr) xs)

  private
    record ↦＊-++-Bundle (n : ℕ) (@0 m : ℕ) (combined : Slice s (n + m)) : Setω₀ where
      field
        left : Slice s n
        right : Slice s m
        @0 eqn :
          (xs : ArrayValue n) (ys : ArrayValue m) →
          combined ↦＊ xs ArrayValue.++ ys ≡ω₀ left ↦＊ xs & right ↦＊ ys
    open ↦＊-++-Bundle
    ↦＊-++ : (n : ℕ) (@0 m : ℕ) (combined : Slice s (n + m)) → ↦＊-++-Bundle n m combined
    ↦＊-++ n       m combined .left  = combined [ 0 ∶+ n because +-monoʳ-≤ n z≤n ]
    ↦＊-++ n       m combined .right = combined [ n ∶+ m because subst (_≤ n + m) (+-comm n m) ≤-refl ]
    ↦＊-++ zero    m combined .eqn   []       ys = reflω₀
    ↦＊-++ (suc n) m combined .eqn   (x ∷ xs) ys =
      let left′ = _ in
      congω₀ (* combined ↦ x ⨾_)
        (    ↦＊-++ n m (++ combined) .eqn xs ys
         ∙ω₀ congω₀↑ (λ s → left′ ↦＊ xs & s ↦＊ ys) (eqSlice refl refl (+-suc n _)))
  module ↦＊-++ (n : ℕ) (@0 m : ℕ) (combined : Slice s (n + m)) = ↦＊-++-Bundle (↦＊-++ n m combined)
