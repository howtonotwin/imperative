{-# OPTIONS --safe #-}
module Imperative.Lemmas where

open import Agda.Primitive
open import Data.List as List hiding ([_])
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.AllPairs hiding (module AllPairs)
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

import Imperative.Specifications
open import LargeEq

module Specifications (StateThread : Setω₀) (Array : StateThread → @0 ℕ → Set lzero) where
  open Imperative.Specifications StateThread Array

  liveRefs& : {s : StateThread} (xs : Condition s) (ys : Condition s) → liveRefs (xs & ys) ≡ liveRefs xs ++ liveRefs ys
  liveRefs& 𝟏         ys = refl
  liveRefs& (x ⨾⨾ xs) ys = cong (x ∷_) (liveRefs& xs ys)

  assoc& : {s : StateThread} (l m r : Condition s) → (l & m) & r ≡ω₀ l & m & r
  assoc& 𝟏        m r = reflω₀
  assoc& (v ⨾⨾ l) m r = congω₀ (v ⨾⨾_) (assoc& l m r)

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

  map⁻ :
    ∀ {ℓB ℓS} {B : Set ℓB} {S : Rel B ℓS} {f : A → B} {xs : List A} →
    (∀ {x y} → S (f x) (f y) → R x y) → AllPairs S (List.map f xs) → AllPairs R xs
  map⁻ {xs = []}     f []       = []
  map⁻ {xs = x ∷ xs} f (p ∷ ps) = All.gmap⁻ f p ∷ map⁻ f ps
