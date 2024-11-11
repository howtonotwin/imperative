{-# OPTIONS --safe #-}
module Imperative.Restructuring where

open import Agda.Primitive
open import Data.Nat
open import Relation.Binary.PropositionalEquality

open import LargeEq

open import Imperative.Condition

module _ {Ref : Set lzero} where
  infixr -1 [_]&[_]⨾[_]⨾⨾_
  data Restructuring : Condition Ref → Condition Ref → Setω₀ where
    [_]╳ : (discards : Condition Ref) → Restructuring discards 𝟏
    [_]&[_]⨾[_]⨾⨾_ :
      ∀ (l : Condition Ref)
      (v : Ref) {ℓ} {A : Set ℓ} {x : A}
      (r : Condition Ref) {rest : Condition Ref} →
      Restructuring (l & r) rest →
      Restructuring (l & v ↦ x ⨾ r) (v ↦ x ⨾ rest)
  pattern ╳ = [ _ ]╳
  pattern ∎ = [ 𝟏 ]╳

  infixr -1 [_]&[_]↦[_]⨾[_]⨾⨾_
  [_]&[_]↦[_]⨾[_]⨾⨾_ :
      ∀ (l : Condition Ref)
      (v : Ref) {ℓ} {A : Set ℓ} {x y : A} (e : x ≡ y)
      (r : Condition Ref) {rest : Condition Ref} →
      Restructuring (l & r) rest →
      Restructuring (l & v ↦ x ⨾ r) (v ↦ y ⨾ rest)
  [ l ]&[ v ]↦[ refl ]⨾[ r ]⨾⨾ p = [ l ]&[ v ]⨾[ r ]⨾⨾ p

  [_]↦[_]∎ : ∀ (v : Ref) {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → Restructuring (v ↦ x ⨾ 𝟏) (v ↦ y ⨾ 𝟏)
  [_]↦[_]∎ = [ 𝟏 ]&[_]↦[_]⨾[ 𝟏 ]⨾⨾ ∎

  [_]∎ : (cond : Condition Ref) → Restructuring cond cond
  [ 𝟏         ]∎ = ∎
  [ v ⨾⨾ cond ]∎ = [ 𝟏 ]&[ v ]⨾[ cond ]⨾⨾ [ cond ]∎
  [!_!]∎ : {pre post : Condition Ref} → pre ≡ω₀ post → Restructuring pre post
  [! reflω₀ !]∎ = [ _ ]∎

  infixr -1 [_]&[_]&[_]⨾⨾_
  [_]&[_]&[_]⨾⨾_ :
    (l m r : Condition Ref) {rest : Condition Ref} →
    Restructuring (l & r) rest →
    Restructuring (l & m & r) (m & rest)
  [ l ]&[ 𝟏      ]&[ r ]⨾⨾ p = p
  [ l ]&[ v ⨾⨾ m ]&[ r ]⨾⨾ p = [ l ]&[ v ]⨾[ m & r ]⨾⨾ [ l ]&[ m ]&[ r ]⨾⨾ p

  discards : {pre post : Condition Ref} → Restructuring pre post → Condition Ref
  discards [ discards ]╳           = discards
  discards ([ l ]&[ v ]⨾[ r ]⨾⨾ p) = discards p
