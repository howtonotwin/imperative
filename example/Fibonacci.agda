{-# OPTIONS --safe #-}
module Fibonacci where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Unit
open import Function.Strict renaming (_$!_ to infixl 9999 _!!_)
open import Relation.Binary.PropositionalEquality renaming (trans to infixl 1 _∙_)

import Imperative
import Imperative.Automation.SmartDo
open import Realizer

-- a functional specification, inefficient and therefore erased
@0 fib : ℕ → ℕ
fib 0             = 0
fib 1             = 1
fib (suc (suc n)) = fib n + fib (suc n)

-- the imperative implementation of fib
-- (generalized over the implementation of imperative programming itself, thus
-- preserving --safe)
module _ (I : Imperative.Impl) where
  open Imperative.Impl I hiding (_>>=_; _>>_; return)
  open Imperative.Automation.SmartDo I
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
    -- restructure is a no-op, but its pre- and post-conditions may differ
    -- the one argument is a proof that the post-condition is equivalent to a
    -- piece of the precondition
    -- the allowed "moves" in such a proof (value of type Restructuring) are
    -- * [_]&[_]↦[_]⨾[_]⨾⨾_: reorder assignment to reference to front while
    --   replacing its value specification with an equivalent one, then use
    --   rest of proof to produce the rest of the post-condition
    -- * ∎: discard any pre-condition to achieve post-condition 𝟏 (must be the
    --   last step of a proof).
    -- replacing its specified value with
    restructure ([ 𝟏 ]&[ lo ]↦[ eqLo ]⨾[ hi ⨾⨾ 𝟏 ]⨾⨾ [ 𝟏 ]&[ hi ]↦[ eqHi ]⨾[ 𝟏 ]⨾⨾ ∎)
  fibWork n lo hi (suc m) eqLo eqHi = do
    -- SmartDo uses reflection to automatically insert uses of the frame rule
    -- this hides a _lot_ of boilerplate even in this example!
    oldLo ← read lo
    oldHi ← read hi
    writeRealized hi !! ⦇ oldLo + oldHi ⦈ -- be strict or suffer a space leak!
    writeRealized lo oldHi
    fibWork (suc n) lo hi m (cong fib (+-suc m n) ∙ eqLo) (cong fib (+-suc m (suc n)) ∙ eqHi)

  -- the stuff that goes around the loop
  calcFib : {s : StateThread} (n : ℕ) → Program s (Realizer (fib n)) 𝟏 (λ _ → 𝟏)
  calcFib zero    = return (λ _ → 𝟏) ⦇ 0 ⦈
  calcFib (suc n) = do
    lo ← init ⦇ 0 ⦈
    hi ← init ⦇ 1 ⦈
    fibWork 0 lo hi n refl refl
    ret ← read hi
    restructure [ lo ⨾⨾ hi ⨾⨾ 𝟏 ]╳
    -- return can generalize the program state over the returned value
    -- in this case we specify that the returned value should not replace any
    -- part of the state (which is empty!)
    return (λ _ → 𝟏) (rethink ret (cong fib (+-comm n 1)))

  -- seal away the imperativeness
  fib′ : ℕ → ℕ
  fib′ n = realize (runProgram (calcFib n))

  -- note that the proof that the imperative program is correct is part of the program text
  @0 fib′-correct : (n : ℕ) → fib′ n ≡ fib n
  fib′-correct n = realizes (runProgram (calcFib n))
