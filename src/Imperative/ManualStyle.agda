{-# OPTIONS --safe #-}
import Imperative
module Imperative.ManualStyle (I : Imperative.Impl) where

open Imperative.Impl I hiding (frame) public
open Imperative.Specifications StateThread Array public
open import Imperative.Slice renaming (Slice to GenSlice; Ref to GenRef) public
open import Imperative.Condition renaming (Condition to GenCondition) public
open import Imperative.Restructuring public
open import Imperative.Framing public

frame :
  ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 pre focus side : Condition s} {@0 post : A → Condition s} →
  @0 Framing pre focus side → Program s A focus post → Program s A pre (λ x → post x & side)
frame f p = do
  restructure (cancelFraming f)
  Imperative.Impl.frame I _ p
