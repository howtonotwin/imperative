{-# OPTIONS --safe #-}
open import Imperative
module Imperative.Automation.SmartDo (I : Imperative.Impl) (let module I = Imperative.Impl I) where

open import Data.Unit

open import Imperative.Automation.Solvers

open I hiding (_>>=_; _>>_; return)

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

-- under SmartDo, this is more effective than restructure
discard : ∀ {s : StateThread} (@0 cond : Condition s) → Program s ⊤ cond λ _ → 𝟏
discard _ = restructure ∎

-- similarly, the condition affected by return generally needs to be explicit
return : ∀ {s : StateThread} {ℓ} {A : Set ℓ} (@0 cond : A → Condition s) (x : A) → Program s A (cond x) cond
return _ x = I.return x
