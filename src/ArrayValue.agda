{-# OPTIONS --safe #-}
module ArrayValue where

open import Agda.Primitive
open import Data.Nat
import Data.Vec as Vec
open Vec using (Vec; []; _∷_)

open import LargeEq

private
  module Contents where
    infixr 5 _∷_
    data ArrayValue : (n : ℕ) → Setω₀ where
      []  : ArrayValue zero
      _∷_ : ∀ {n} {ℓ} {A : Set ℓ} (x : A) (xs : ArrayValue n) → ArrayValue (suc n)
open Contents hiding (module ArrayValue) public

replicate : ∀ {ℓ} {A : Set ℓ} (n : ℕ) (x : A) → ArrayValue n
replicate zero    _ = []
replicate (suc n) x = x ∷ replicate n x

infixr 5 _++_
_++_ : {n m : ℕ} → ArrayValue n → ArrayValue m → ArrayValue (n + m)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

infixl 5 _∷ʳ_
_∷ʳ_ : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → ArrayValue n → A → ArrayValue (suc n)
[]       ∷ʳ y = y ∷ []
(x ∷ xs) ∷ʳ y = x ∷ (xs ∷ʳ y)

vec : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → Vec A n → ArrayValue n
vec []       = []
vec (x ∷ xs) = x ∷ vec xs

vec++ : ∀ {ℓ} {A : Set ℓ} {n m : ℕ} (xs : Vec A n) (ys : Vec A m) → vec (xs Vec.++ ys) ≡ω₀ vec xs ++ vec ys
vec++ []       ys = reflω₀
vec++ (x ∷ xs) ys = congω₀ (x ∷_) (vec++ xs ys)

vec∷ʳ : ∀ {ℓ} {A : Set ℓ} {n : ℕ} (xs : Vec A n) (y : A) → vec (xs Vec.∷ʳ y) ≡ω₀ vec xs ∷ʳ y
vec∷ʳ []       y = reflω₀
vec∷ʳ (x ∷ xs) y = congω₀ (x ∷_) (vec∷ʳ xs y)
