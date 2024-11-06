{-# OPTIONS --safe #-}
import Imperative
module Imperative.ManualStyle (I : Imperative.Impl) where

private module I = Imperative.Impl I
open I hiding (frame; module Condition; module Framing; module Restructuring) public
open I.Condition public
open I.Framing public
open I.Restructuring public

frame :
  ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 pre focus side : Condition s} {@0 post : A → Condition s} →
  @0 Framing pre focus side → Program s A focus post → Program s A pre (λ x → post x & side)
frame f p = do
  restructure (cancelFraming f)
  I.frame _ p
