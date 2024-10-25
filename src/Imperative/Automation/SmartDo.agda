{-# OPTIONS --safe #-}
open import Imperative
module Imperative.Automation.SmartDo (I : Imperative.Impl) (let module I = Imperative.Impl I) where

open import Data.Unit

import Imperative.Lemmas as Lemmas
open import Imperative.Automation.Solvers

open I hiding (_>>=_; _>>_; return)
open Lemmas.Spec StateThread Ref

private
  reframe :
    ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 pre focus : Condition s} {@0 post : A → Condition s}
    (@0 r : Restructuring pre focus) → Program s A focus post → Program s A pre (λ x → post x & discards r)
  reframe r p = restructure (nondestructive r) I.>> frame _ p

_>>=_ :
  ∀ {s : StateThread} {ℓA ℓB} {A : Set ℓA} {B : Set ℓB}
  {@0 pre focus : Condition s} {@0 mid : A → Condition s} {@0 post : B → Condition s}
  {@(tactic restructure!-tactic) @0 r : Restructuring pre focus} →
  Program s A focus mid → ((x : A) → Program s B (mid x & discards r) post) → Program s B pre post
_>>=_ {r = r} p q = reframe r p I.>>= q
_>>_ :
    ∀ {s : StateThread} {ℓA ℓB} {A : Set ℓA} {B : Set ℓB}
    {@0 pre focus : Condition s} {@0 mid : A → Condition s} {@0 post : B → Condition s}
    {@(tactic restructure!-tactic) @0 r : Restructuring pre focus} →
    Program s A focus mid → ({x : A} → Program s B (mid x & discards r) post) → Program s B pre post
_>>_ {r = r} p q = reframe r p I.>> q

-- the condition affected by return seems to need to be explicit
return : ∀ {s : StateThread} {ℓ} {A : Set ℓ} (@0 cond : A → Condition s) (x : A) → Program s A (cond x) cond
return _ x = I.return x
