{-# OPTIONS --safe #-}
-- reexports of auxiliary data types used in the definition of Imperative.Impl
-- specialized in terms of certain fields of Imperative.Impl
open import Agda.Primitive
open import Data.Nat
module Imperative.Specifications (StateThread : Setω₀) (Array : StateThread → @0 ℕ → Set lzero) where

open import Imperative.Slice renaming (Slice to GenSlice; Ref to GenRef)
open import Imperative.Condition renaming (Condition to GenCondition)

Slice : StateThread → @0 ℕ → Set lzero
Slice s = GenSlice (Array s)
Ref : StateThread → Set lzero
Ref s = GenRef (Array s)

Condition : StateThread → Setω₀
Condition s = GenCondition (Ref s)
