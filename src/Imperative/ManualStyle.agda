{-# OPTIONS --safe #-}
import Imperative
module Imperative.ManualStyle (I : Imperative.Impl) where

import Imperative.Framing
import Imperative.Restructuring

private module I = Imperative.Impl I
open I hiding (frame) public
open Imperative.Framing StateThread Array public
open Imperative.Restructuring StateThread Array hiding (Restructuring) public

frame :
  ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 pre focus side : Condition s} {@0 post : A → Condition s} →
  @0 Framing pre focus side → Program s A focus post → Program s A pre (λ x → post x & side)
frame f p = do
  I.restructure (cancelFraming f)
  I.frame _ p
