{-# OPTIONS --safe #-}
module Fibonacci where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Unit
open import Function.Strict renaming (_$!_ to infixl -10 _!!_)
open import Relation.Binary.PropositionalEquality renaming (trans to infixl 1 _∙_)

open import Realizer

import Imperative
import Imperative.AutomaticStyle

-- a functional specification, inefficient and therefore erased
@0 fib : ℕ → ℕ
fib 0             = 0
fib 1             = 1
fib (suc (suc n)) = fib n + fib (suc n)

-- the imperative implementation of fib
-- (generalized over the implementation of imperative programming itself, thus
-- preserving --safe)
module _ (I : Imperative.Impl) where
  open Imperative.AutomaticStyle I
  -- main loop, which takes condition (lo ↦ fib n ⨾ hi ↦ fib (suc n)) to the
  -- condition (lo ↦ fib (m + n) ⨾ hi ↦ fib (m + suc m))
  -- note that this is not an imperative loop that mutates a counter stored in a
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
  fibWork n lo hi zero    eqLo eqHi = do
    -- restructure is a no-op, but its pre- and post-conditions may differ
    -- the one argument is a proof that the post-condition is equivalent to a
    -- piece of the precondition
    -- the primitive "moves" in such a proof (constructors of Restructuring) are
    -- * [_]&[_]⨾[_]⨾⨾_: naming the arguments l, v, r, p, reorder the assignment
    --   for reference v in the precondition (l & v ⨾⨾ r) to the front, then use
    --   the proof p to produce the rest of the post-condition from (l & r)
    -- * [_]╳: discard the given pre-condition to achieve post-condition 𝟏 (must
    --   be the last step of a proof)
    -- here only the derived move [_]↦[_]∎ is used: "apply equality to variable"
    restructure [ lo ]↦[ eqLo ]∎
    restructure [ hi ]↦[ eqHi ]∎
    -- SmartDo uses reflection to automatically insert uses of the frame rule on
    -- each use of _>>=_ or _>>_ (this makes the above two lines work)
    -- this hides a _lot_ of boilerplate: compare to FibonacciManual
    -- an explicit return (as opposed to making a tail call) can also be
    -- necessary at the end of a do to rearrange the state
    return tt
  fibWork n lo hi (suc m) eqLo eqHi = do
    oldLo ← read lo
    oldHi ← read hi
    writeRealized hi !! ⦇ oldLo + oldHi ⦈ -- be strict or suffer a space leak!
    writeRealized lo oldHi
    fibWork (suc n) lo hi m (cong fib (+-suc m n) ∙ eqLo) (cong fib (+-suc m (suc n)) ∙ eqHi)

  -- the stuff that goes around the loop
  calcFib : {s : StateThread} (n : ℕ) → Program s (Realizer (fib n)) 𝟏 (λ _ → 𝟏)
  calcFib zero    = return ⦇ 0 ⦈
  calcFib (suc n) = do
    lo ← init ⦇ 0 ⦈
    hi ← init ⦇ 1 ⦈
    fibWork 0 lo hi n refl refl
    restructure [ hi ]↦[ cong fib (+-comm n 1) ]∎
    ret ← read hi
    return ret

  -- seal away the imperativeness
  fib′ : ℕ → ℕ
  fib′ n = realize (runProgram (calcFib n))

  -- note that the proof that the imperative program is correct is part of the program text
  @0 fib′-correct : (n : ℕ) → fib′ n ≡ fib n
  fib′-correct n = realizes (runProgram (calcFib n))
