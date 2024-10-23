{-# OPTIONS --safe #-}
module Erased where

open import Agda.Primitive

private
  module Contents where
    record Erased {ℓ} (@0 A : Set ℓ) : Set ℓ where
      constructor erased
      field @0 erasedly : A
    open Erased public
open Contents hiding (module Erased) public
