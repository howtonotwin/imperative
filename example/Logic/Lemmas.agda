{-# OPTIONS --safe #-}
module Logic.Lemmas where

open import Agda.Primitive
open import Data.List as DList hiding (module List)
open import Data.List.Relation.Unary.Linked
import Data.List.Relation.Unary.Sorted.TotalOrder
open import Data.Maybe
open import Data.Maybe.Relation.Binary.Connected hiding (refl)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Vec as DVec hiding (module Vec)
open import Relation.Binary.PropositionalEquality

open import ArrayValue
open import LargeEq

import Imperative
import Imperative.Condition

open Data.List.Relation.Unary.Sorted.TotalOrder ≤-totalOrder

module Sorted where
  ++⁻ : ∀ {xs ys} → Sorted (xs DList.++ ys) → Sorted xs × Connected _≤_ (DList.last xs) (DList.head ys) × Sorted ys
  ++⁻ {[]}           {[]}     []        = []  , nothing      , []
  ++⁻ {[]}           {y ∷ ys} p         = []  , nothing-just , p
  ++⁻ {x₁ ∷ []}      {[]}     [-]       = [-] , just-nothing , []
  ++⁻ {x₁ ∷ []}      {y ∷ ys} (p₁ ∷ p₂) = [-] , just p₁      , p₂
  ++⁻ {x₁ ∷ x₂ ∷ xs} {ys}     (p₁ ∷ p₂) =
    let q₁ , q₂ , q₃ = ++⁻ p₂ in
    p₁ ∷ q₁ , q₂ , q₃

module Vec where
  toList-∷ʳ : ∀ {ℓ} {A : Set ℓ} {n : ℕ} (xs : Vec A n) (y : A) → DVec.toList (xs DVec.∷ʳ y) ≡ DVec.toList xs DList.∷ʳ y
  toList-∷ʳ []       y = refl
  toList-∷ʳ (x ∷ xs) y = cong (x ∷_) (toList-∷ʳ xs y)

module List where
  last-∷ʳ : ∀ {ℓ} {A : Set ℓ} (xs : List A) (y : A) → DList.last (xs DList.∷ʳ y) ≡ just y
  last-∷ʳ []           y = refl
  last-∷ʳ (_ ∷ [])     y = refl
  last-∷ʳ (_ ∷ x ∷ xs) y = last-∷ʳ (x ∷ xs) y

module Condition (I : Imperative.Impl) (open Imperative.Impl I using (StateThread; Array)) {s : StateThread} where
  open Imperative.Condition StateThread Array
