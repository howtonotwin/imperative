{-# OPTIONS --safe --warning=noUnsupportedIndexedMatch #-}
module Imperative.Lemmas where

open import Agda.Primitive
open import Data.List hiding ([_])
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.AllPairs hiding (module AllPairs)
open import Data.Product
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

import Imperative

module Spec (StateThread : SSetω₀) (Ref : StateThread → Set lzero) where
  open Imperative.Spec StateThread Ref

  liveRefs& :
    ∀ {s : StateThread} {ℓ₁ ℓ₂} (xs : Condition s ℓ₁) (ys : Condition s ℓ₂) →
    liveRefs (xs & ys) ≡ liveRefs xs ++ liveRefs ys
  liveRefs& 𝟏         ys = refl
  liveRefs& (x ⨾⨾ xs) ys = cong (x ∷_) (liveRefs& xs ys)

module ∈ {ℓ} {A : Set ℓ} where
  ++⁺ : {xs ys : List A} {x : A} → x ∈ xs ⊎ x ∈ ys → x ∈ xs ++ ys
  ++⁺ = [ ∈-++⁺ˡ , ∈-++⁺ʳ _ ]

module AllPairs {ℓA ℓR} {A : Set ℓA} {R : Rel A ℓR} where
  ++⁻ : {xs ys : List A} → AllPairs R (xs ++ ys) → AllPairs R xs × AllPairs R ys × All (λ x → All (R x) ys) xs
  ++⁻ {[]}     ps       = [] , ps , []
  ++⁻ {x ∷ xs} (p ∷ ps) =
    let l , r , lrs = ++⁻ ps in
    let ll , lr = All.++⁻ xs p in
    ll ∷ l , r , lr ∷ lrs
