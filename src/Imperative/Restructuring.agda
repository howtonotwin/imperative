{-# OPTIONS --safe #-}
open import Agda.Primitive
open import Data.Nat
module Imperative.Restructuring (StateThread : Setω₀) (Array : StateThread → @0 ℕ → Set lzero) where

open import Relation.Binary.PropositionalEquality

open import Imperative.Condition StateThread Array
open import LargeEq

module _ {s : StateThread} where
  infixr -1 [_]&[_]⨾[_]⨾⨾_
  data Restructuring : Condition s → Condition s → Setω₀ where
    [_]╳ : (discards : Condition s) → Restructuring discards 𝟏
    [_]&[_]⨾[_]⨾⨾_ :
      ∀ (l : Condition s)
      (v : Ref s) {ℓ} {A : Set ℓ} {x : A}
      (r : Condition s) {rest : Condition s} →
      Restructuring (l & r) rest →
      Restructuring (l & v ↦ x ⨾ r) (v ↦ x ⨾ rest)
  pattern ╳ = [ _ ]╳
  pattern ∎ = [ 𝟏 ]╳

  infixr -1 [_]&[_]↦[_]⨾[_]⨾⨾_
  [_]&[_]↦[_]⨾[_]⨾⨾_ :
      ∀ (l : Condition s)
      (v : Ref s) {ℓ} {A : Set ℓ} {x y : A} (e : x ≡ y)
      (r : Condition s) {rest : Condition s} →
      Restructuring (l & r) rest →
      Restructuring (l & v ↦ x ⨾ r) (v ↦ y ⨾ rest)
  [ l ]&[ v ]↦[ refl ]⨾[ r ]⨾⨾ p = [ l ]&[ v ]⨾[ r ]⨾⨾ p

  [_]↦[_]∎ : ∀ (v : Ref s) {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → Restructuring (v ↦ x ⨾ 𝟏) (v ↦ y ⨾ 𝟏)
  [_]↦[_]∎ = [ 𝟏 ]&[_]↦[_]⨾[ 𝟏 ]⨾⨾ ∎

  [_]∎ : (cond : Condition s) → Restructuring cond cond
  [ 𝟏         ]∎ = ∎
  [ v ⨾⨾ cond ]∎ = [ 𝟏 ]&[ v ]⨾[ cond ]⨾⨾ [ cond ]∎
  [!_!]∎ : {pre post : Condition s} → pre ≡ω₀ post → Restructuring pre post
  [! reflω₀ !]∎ = [ _ ]∎

  infixr -1 [_]&[_]&[_]⨾⨾_
  [_]&[_]&[_]⨾⨾_ :
    (l m r : Condition s) {rest : Condition s} →
    Restructuring (l & r) rest →
    Restructuring (l & m & r) (m & rest)
  [ l ]&[ 𝟏      ]&[ r ]⨾⨾ p = p
  [ l ]&[ v ⨾⨾ m ]&[ r ]⨾⨾ p = [ l ]&[ v ]⨾[ m & r ]⨾⨾ [ l ]&[ m ]&[ r ]⨾⨾ p
