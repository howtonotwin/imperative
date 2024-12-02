{-# OPTIONS --safe #-}
-- manipulations of an imperative program's heap that can be effected without
-- actually doing anything
-- i.e. reordering (exchange) and forgetting (weakening) parts of a heap
-- description
module Imperative.Restructuring where

open import Agda.Primitive
open import Data.Nat
open import Relation.Binary.PropositionalEquality

open import LargeEq

open import Imperative.Condition

module _ {Ref : Set lzero} where
  -- input output : Condition Ref are related by Restructuring iff there is a way
  -- start from input and arrive at output by reordering and deleting Assignments
  infixr -1 [_]&[_]⨾[_]⨾⨾_
  data Restructuring : Condition Ref → Condition Ref → Setω₀ where
    -- the contents of any amount of memory can be forgotten about
    [_]╳ : (discards : Condition Ref) → Restructuring discards 𝟏
    -- v : Ref may be placed at the head of the output if the input decomposes
    -- into (l & v ⨾⨾ r), and the rest of the output can be produced by
    -- Restructuring the remainder (l & r) of the input
    -- note that v cannot be duplicated
    [_]&[_]⨾[_]⨾⨾_ :
      ∀ (l : Condition Ref)
      (v : Ref) {ℓ} {A : Set ℓ} {x : A}
      (r : Condition Ref) {rest : Condition Ref} →
      Restructuring (l & r) rest →
      Restructuring (l & v ↦ x ⨾ r) (v ↦ x ⨾ rest)
  -- essentially a list of the references wanted in the output, in the output
  -- order, annotated with locations in the (reduced) input
  -- convenient: if the input contains all distinct Refs, then for any possible
  -- output there is (basically) only one way to write a Restructuring

  -- example:
  module _ (x y z : Ref) where
    _ : Restructuring (x ↦ 1 ⨾ y ↦ 2 ⨾ z ↦ 3 ⨾ 𝟏) (z ↦ 3 ⨾ x ↦ 1 ⨾ 𝟏)
    -- think in the following steps
    -- 1. to get (z ↦ 3) into the output, note (z ↦ 3) appears in the input with
    --    (x ↦ 1 ⨾ y ↦ 2 ⨾ 𝟏) to left and 𝟏 to right. apply
    --    [ x ⨾⨾ y ⨾⨾ 𝟏 ]&[ z ]⨾[ 𝟏 ]⨾⨾_
    -- 2. next, want (x ↦ 1) from reduced input (x ↦ 1 ⨾ y ↦ 2 ⨾ 𝟏). apply
    --    [ 𝟏 ]&[ x ]⨾[ y ⨾⨾ 𝟏 ]⨾⨾_
    -- 3. finally, discard y ↦ 2 ⨾ 𝟏: [ y ⨾⨾ 𝟏 ]╳
    _ = [ x ⨾⨾ y ⨾⨾ 𝟏 ]&[ z ]⨾[ 𝟏 ]⨾⨾ [ 𝟏 ]&[ x ]⨾[ y ⨾⨾ 𝟏 ]⨾⨾ [ y ⨾⨾ 𝟏 ]╳

  -- shorthand for ignoring/inferring what is discarded
  pattern ╳ = [ _ ]╳
  -- shorthand for no discards
  pattern ∎ = [ 𝟏 ]╳

  -- Restructuring automatically respects propositional equality
  -- version of `[_]&[_]⨾[_]⨾⨾_` that also rewrites value at the chosen location
  infixr -1 [_]&[_]↦[_]⨾[_]⨾⨾_
  [_]&[_]↦[_]⨾[_]⨾⨾_ :
      ∀ (l : Condition Ref)
      (v : Ref) {ℓ} {A : Set ℓ} {x y : A} (e : x ≡ y)
      (r : Condition Ref) {rest : Condition Ref} →
      Restructuring (l & r) rest →
      Restructuring (l & v ↦ x ⨾ r) (v ↦ y ⨾ rest)
  [ l ]&[ v ]↦[ refl ]⨾[ r ]⨾⨾ p = [ l ]&[ v ]⨾[ r ]⨾⨾ p

  -- specialization of above to lone references
  [_]↦[_]∎ : ∀ (v : Ref) {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → Restructuring (v ↦ x ⨾ 𝟏) (v ↦ y ⨾ 𝟏)
  [_]↦[_]∎ = [ 𝟏 ]&[_]↦[_]⨾[ 𝟏 ]⨾⨾ ∎

  -- identity Restructuring
  [_]∎ : (cond : Condition Ref) → Restructuring cond cond
  [ 𝟏         ]∎ = ∎
  [ v ⨾⨾ cond ]∎ = [ 𝟏 ]&[ v ]⨾[ cond ]⨾⨾ [ cond ]∎

  -- Restructuring by a Condition equality
  [!_!]∎ : {pre post : Condition Ref} → pre ≡ω₀ post → Restructuring pre post
  [! reflω₀ !]∎ = [ _ ]∎

  -- variant of [_]&[_]⨾[_]⨾⨾_ selecting an entire Condition to keep
  infixr -1 [_]&[_]&[_]⨾⨾_
  [_]&[_]&[_]⨾⨾_ :
    (l m r : Condition Ref) {rest : Condition Ref} →
    Restructuring (l & r) rest →
    Restructuring (l & m & r) (m & rest)
  [ l ]&[ 𝟏      ]&[ r ]⨾⨾ p = p
  [ l ]&[ v ⨾⨾ m ]&[ r ]⨾⨾ p = [ l ]&[ v ]⨾[ m & r ]⨾⨾ [ l ]&[ m ]&[ r ]⨾⨾ p

  -- the Condition being discarded at the end of a Restructuring
  discards : {pre post : Condition Ref} → Restructuring pre post → Condition Ref
  discards [ discards ]╳           = discards
  discards ([ l ]&[ v ]⨾[ r ]⨾⨾ p) = discards p
