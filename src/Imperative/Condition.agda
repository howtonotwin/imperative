{-# OPTIONS --safe #-}
module Imperative.Condition where

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

infix 1 _↦_
record Assignment (Ref : Set lzero) : Setω₀ where
  constructor _↦_
  field
    var : Ref
    {contentLevel} : Level
    {contentType} : Set contentLevel
    content : contentType

infixr 0 _⨾_
data Condition (Ref : Set lzero) : Setω₀ where
  𝟏   : Condition Ref
  _⨾_ : Assignment Ref → Condition Ref → Condition Ref
infixr 0 _⨾⨾_
pattern _⨾⨾_ v r = v ↦ _ ⨾ r
module _ {Ref : Set lzero} where
  liveRefs : Condition Ref → List Ref
  liveRefs 𝟏         = []
  liveRefs (x ⨾⨾ xs) = x ∷ liveRefs xs

  infixr 0 _&_
  _&_ : Condition Ref → Condition Ref → Condition Ref
  𝟏        & ys = ys
  (x ⨾ xs) & ys = x ⨾ xs & ys

  liveRefs-& : (xs : Condition Ref) (ys : Condition Ref) → liveRefs (xs & ys) ≡ liveRefs xs List.++ liveRefs ys
  liveRefs-& 𝟏         ys = refl
  liveRefs-& (x ⨾⨾ xs) ys = cong (x ∷_) (liveRefs-& xs ys)

  assoc& : (l m r : Condition Ref) → (l & m) & r ≡ω₀ l & m & r
  assoc& 𝟏        m r = reflω₀
  assoc& (v ⨾⨾ l) m r = congω₀ (v ⨾⨾_) (assoc& l m r)
module _ {Array : @0 ℕ → Set lzero} where
  open Imperative.Slice

  infix 1 _↦＊_
  _↦＊_ : {@0 n : ℕ} → Slice Array n → ArrayValue n → Condition (Ref Array)
  s ↦＊ []     = 𝟏
  s ↦＊ x ∷ xs = * s ↦ x ⨾ ++ s ↦＊ xs

  ↦＊-∷ʳ :
    ∀ {n : ℕ} {ℓ} {A : Set ℓ} (snoc : Slice Array (suc n)) (xs : ArrayValue n) (y : A) →
    snoc ↦＊ (xs ArrayValue.∷ʳ y) ≡ω₀ snoc [∶-1] ↦＊ xs & snoc [-1] ↦ y ⨾ 𝟏
  ↦＊-∷ʳ snoc []       y = reflω₀
  ↦＊-∷ʳ snoc (x ∷ xs) y =
    congω₀ (* snoc ↦ x ⨾_)
      (↦＊-∷ʳ (++ snoc) xs y ∙ω₀ congω₀↑ (λ r → ++ snoc [∶-1] ↦＊ xs & r ↦ y ⨾ 𝟏) (eqSlice refl refl (+-suc _ _)))
  substSlice-↦＊-cast :
    {n m : ℕ} (e : n ≡ m) (arr : Slice Array n) (xs : ArrayValue m) →
    substSlice e arr ↦＊ xs ≡ω₀ arr ↦＊ ArrayValue.cast (sym e) xs
  substSlice-↦＊-cast {zero}  e arr []       = reflω₀
  substSlice-↦＊-cast {suc n} e arr (x ∷ xs) = congω₀ (* arr ↦ x ⨾_) (substSlice-↦＊-cast (cong pred e) (++ arr) xs)

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
