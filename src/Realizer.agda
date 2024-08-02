{-# OPTIONS --safe #-}
module Realizer where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality

private
  module Contents where
    data Realizer {ℓ} {A : Set ℓ} : @0 A → Set ℓ where
      realized : (x : A) → Realizer x
open Contents hiding (module Realizer) public

realize : ∀ {ℓ} {A : Set ℓ} {@0 x : A} → Realizer x → A
realize (realized x) = x

@0 realizes : ∀ {ℓ} {A : Set ℓ} {@0 x : A} (r : Realizer x) → realize r ≡ x
realizes (realized x) = refl

pure : ∀ {ℓ} {A : Set ℓ} (x : A) → Realizer x
pure = realized
_<*>_ :
  ∀ {ℓA ℓB} {A : Set ℓA} {B : @0 A → Set ℓB} {@0 f : (x : A) → B x} {@0 x : A} →
  Realizer f → Realizer x → Realizer (f x)
realized f <*> realized x = realized (f x)
