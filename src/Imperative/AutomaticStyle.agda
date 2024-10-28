{-# OPTIONS --safe #-}
open import Imperative
module Imperative.AutomaticStyle (I : Imperative.Impl) where

open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Imperative.Solvers
import Imperative.Framing
import Imperative.ManualStyle
import Imperative.Restructuring

private module I = Imperative.Impl I
open I hiding (_>>=_; _>>_; return) public
open Imperative.Framing StateThread Ref
open Imperative.ManualStyle I using () renaming (frame to reframe)
open Imperative.Restructuring StateThread Ref hiding (Restructuring) public

_>>=_ :
  ∀ {s : StateThread} {ℓA ℓB} {A : Set ℓA} {B : Set ℓB}
  {@0 pre focus side : Condition s} {@0 mid : A → Condition s} {@0 post : B → Condition s} →
  {@(tactic framing-tactic) @0 r : Framing pre focus side} →
  Program s A focus mid → ((x : A) → Program s B (mid x & side) post) → Program s B pre post
_>>=_ {r = r} p q = reframe r p I.>>= q
_>>_ :
    ∀ {s : StateThread} {ℓA ℓB} {A : Set ℓA} {B : Set ℓB}
    {@0 pre focus side : Condition s} {@0 mid : A → Condition s} {@0 post : B → Condition s}
    {@(tactic framing-tactic) @0 r : Framing pre focus side} →
    Program s A focus mid → ({x : A} → Program s B (mid x & side) post) → Program s B pre post
_>>_ {r = r} p q = reframe r p I.>> q

return :
  ∀ {s : StateThread} {ℓ} {A : Set ℓ} (x : A)
  {@0 pre : Condition s} {@0 post : A → Condition s}
  {@(tactic restructuring-tactic) @0 r : Restructuring pre (post x)} →
  Program s A pre post
return x {r = r} = restructure r I.>> I.return x
