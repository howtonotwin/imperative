{-# OPTIONS --safe #-}
-- Version of Fibonacci where structural manipulations and framings of the heap
-- are manually written out instead of being automated away
module FibonacciManual where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Unit
open import Function.Strict renaming (_$!_ to infixl -10 _!!_)
open import Relation.Binary.PropositionalEquality renaming (trans to infixl 1 _∙_)

open import Realizer

import Imperative
import Imperative.ManualStyle

@0 fib : ℕ → ℕ
fib 0             = 0
fib 1             = 1
fib (suc (suc n)) = fib n + fib (suc n)

module _ (I : Imperative.Impl) where
  open Imperative.ManualStyle I

  fibWork :
    {s : StateThread} (@0 n : ℕ) (lo hi : Ref s) (m : ℕ)
    {@0 outLo outHi : ℕ} → @0 fib (m + n) ≡ outLo → @0 fib (m + suc n) ≡ outHi →
    Program s ⊤
      (lo ↦ fib n ⨾ hi ↦ fib (suc n) ⨾ 𝟏)
      (λ _ → lo ↦ outLo ⨾ hi ↦ outHi ⨾ 𝟏)
  fibWork n lo hi zero    eqLo eqHi =
    restructure ([ 𝟏 ]&[ lo ]↦[ eqLo ]⨾[ hi ⨾⨾ 𝟏 ]⨾⨾ [ 𝟏 ]&[ hi ]↦[ eqHi ]⨾[ 𝟏 ]⨾⨾ ∎)
  fibWork n lo hi (suc m) eqLo eqHi = do
    oldLo ← reframe (>[ lo ⨾⨾ 𝟏 ]< <& (hi ⨾⨾ 𝟏)) (read lo)
    oldHi ← reframe ((lo ⨾⨾ 𝟏) &> >[ hi ⨾⨾ 𝟏 ]<) (read hi)
    reframe (>[ hi ⨾⨾ 𝟏 ]< <& (lo ⨾⨾ 𝟏)) (writeRealized hi !! ⦇ oldLo + oldHi ⦈)
    reframe ((hi ⨾⨾ 𝟏) &> >[ lo ⨾⨾ 𝟏 ]<) (writeRealized lo oldHi)
    fibWork (suc n) lo hi m (cong fib (+-suc m n) ∙ eqLo) (cong fib (+-suc m (suc n)) ∙ eqHi)

  -- the stuff that goes around the loop
  calcFib : {s : StateThread} (n : ℕ) → Program s (Realizer (fib n)) 𝟏 (λ _ → 𝟏)
  calcFib zero    = return ⦇ 0 ⦈
  calcFib (suc n) = do
    hi ← init ⦇ 1 ⦈
    lo ← reframe ((hi ⨾⨾ 𝟏) &> >𝟏<) (init ⦇ 0 ⦈)
    fibWork 0 lo hi n refl refl
    restructure ([ lo ⨾⨾ 𝟏 ]&[ hi ]↦[ cong fib (+-comm n 1) ]⨾[ 𝟏 ]⨾⨾ ╳)
    ret ← read hi
    restructure ╳
    return ret

  fib′ : ℕ → ℕ
  fib′ n = realize (runProgram (calcFib n))

  @0 fib′-correct : (n : ℕ) → fib′ n ≡ fib n
  fib′-correct n = realizes (runProgram (calcFib n))
