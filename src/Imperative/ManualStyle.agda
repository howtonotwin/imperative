{-# OPTIONS --safe #-}
import Imperative
module Imperative.ManualStyle (I : Imperative.Impl) where

open Imperative.Impl I public
open import Imperative.Slice renaming (Slice to GenSlice; Ref to GenRef) public
open import Imperative.Condition renaming (Condition to GenCondition) public
open import Imperative.Restructuring public
open import Imperative.Framing public
