{-# OPTIONS --safe #-}
module ArrayValue where

open import Agda.Primitive
open import Data.Nat

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
