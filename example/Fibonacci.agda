{-# OPTIONS --safe #-}
module Fibonacci where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Unit
open import Function.Strict renaming (_$!_ to infixl 9999 _!!_)
open import Relation.Binary.PropositionalEquality renaming (trans to infixl 1 _∙_)

import Imperative
open import Realizer

-- a functional specification, inefficient and therefore erased
-- erasure also permits the usage of cubical's Glue, if desired
@0 fib : ℕ → ℕ
fib 0             = 0
fib 1             = 1
fib (suc (suc n)) = fib n + fib (suc n)

-- the imperative implementation of fib
-- (generalized over the implementation of imperative programming itself, thus
-- preserving --safe)
module _ (I : Imperative.Impl) (open Imperative.Impl I) where
  -- main loop, which takes condition (lo ↦ fib n ⨾ hi ↦ fib (suc n)) to the
  -- condition (lo ↦ fib (m + n) ⨾ hi ↦ fib (m + suc m))
  -- note that this is not an imperative loop that mutates a value stored in a
  -- fixed location
  -- it is simpler to purely unroll the loop by recursing on m
  -- note that in order to keep this tail recursive, there need to be
  -- accumulators that hold (erased) *proofs* (eqLo and eqHi)
  -- else, there would be a restructure call after the recursive call
  -- (ideally, there would be a way to force Agda/GHC to specialize a function
  -- recursively on an Imperative.Impl, since restructure is a no-op for ST
  -- then there would be no need to manage the tail recursion manually)
  fibWork :
    {s : StateThread} (@0 n : ℕ) (lo hi : Ref s) (m : ℕ)
    {@0 outLo outHi : ℕ} → @0 fib (m + n) ≡ outLo → @0 fib (m + suc n) ≡ outHi →
    Program s ⊤
      (lo ↦ fib n ⨾ hi ↦ fib (suc n) ⨾ 𝟏)
      (λ _ → lo ↦ outLo ⨾ hi ↦ outHi ⨾ 𝟏)
  fibWork n lo hi zero    eqLo eqHi =
    restructure ([ 𝟏 ]&[ lo ]↦[ eqLo ]⨾[ hi ⨾⨾ 𝟏 ]⨾⨾ [ 𝟏 ]&[ hi ]↦[ eqHi ]⨾[ 𝟏 ]⨾⨾ ∎)
  fibWork n lo hi (suc m) eqLo eqHi = do
    oldLo ← frame (hi ⨾⨾ 𝟏) (read lo)
    restructure ([ lo ⨾⨾ 𝟏 ]&[ hi ]⨾[ 𝟏 ]⨾⨾ [ 𝟏 ]&[ lo ]⨾[ 𝟏 ]⨾⨾ ∎)
    oldHi ← frame (lo ⨾⨾ 𝟏) (read hi)
    frame (lo ⨾⨾ 𝟏) (writeRealized hi !! ⦇ oldLo + oldHi ⦈) -- be strict or suffer a space leak!
    restructure ([ hi ⨾⨾ 𝟏 ]&[ lo ]⨾[ 𝟏 ]⨾⨾ [ 𝟏 ]&[ hi ]⨾[ 𝟏 ]⨾⨾ ∎)
    frame (hi ⨾⨾ 𝟏) (writeRealized lo oldHi)
    fibWork (suc n) lo hi m (cong fib (+-suc m n) ∙ eqLo) (cong fib (+-suc m (suc n)) ∙ eqHi)

  -- the stuff that goes around the loop
  calcFib : {s : StateThread} (n : ℕ) → Program s (Realizer (fib n)) 𝟏 (λ _ → 𝟏)
  calcFib zero    = return ⦇ 0 ⦈
  calcFib (suc n) = do
    hi ← init ⦇ 1 ⦈
    lo ← frame (hi ⨾⨾ 𝟏) (init ⦇ 0 ⦈)
    fibWork 0 lo hi n refl refl
    restructure ([ lo ⨾⨾ 𝟏 ]&[ hi ]↦[ cong fib (+-comm n 1) ]⨾[ 𝟏 ]⨾⨾ ∎)
    ret ← read hi
    restructure ∎
    return ret

  -- seal away the imperativeness
  fib′ : ℕ → ℕ
  fib′ n = realize (runProgram (calcFib n))

  -- note that the proof of correctness is intercalated with the program text
  @0 fib′-correct : (n : ℕ) → fib′ n ≡ fib n
  fib′-correct n = realizes (runProgram (calcFib n))
