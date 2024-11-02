{-# OPTIONS --safe #-}
module LargeEq where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality

infix -2 _≡ω₀_
data _≡ω₀_ {A : Setω₀} (x : A) : A → Setω₀ where
  reflω₀ : x ≡ω₀ x
congω₀ : {A B : Setω₀} (f : A → B) {x y : A} → x ≡ω₀ y → f x ≡ω₀ f y
congω₀ f reflω₀ = reflω₀
infixl 1 _∙ω₀_
_∙ω₀_ : {A : Setω₀} {x y z : A} → x ≡ω₀ y → y ≡ω₀ z → x ≡ω₀ z
reflω₀ ∙ω₀ reflω₀ = reflω₀
symω₀ : {A : Setω₀} {x y : A} → x ≡ω₀ y → y ≡ω₀ x
symω₀ reflω₀ = reflω₀

congω₀↑ : ∀ {ℓ} {A : Set ℓ} {B : Setω₀} (f : A → B) {x y : A} → x ≡ y → f x ≡ω₀ f y
congω₀↑ f refl = reflω₀
