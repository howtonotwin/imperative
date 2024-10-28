{-# OPTIONS --safe #-}
open import Agda.Primitive
module Imperative.Restructuring (StateThread : Setω₀) (Ref : StateThread → Set lzero) where

open import Relation.Binary.PropositionalEquality

import Imperative
private module Spec = Imperative.Spec StateThread Ref
open Spec using (Restructuring; [_]╳; [_]&[_]⨾[_]⨾⨾_; ╳; ∎) public
open Spec

infixr -1 [_]&[_]↦[_]⨾[_]⨾⨾_
[_]&[_]↦[_]⨾[_]⨾⨾_ :
    ∀ {s : StateThread}
    (l : Condition s)
    (v : Ref s) {ℓ} {A : Set ℓ} {x y : A} (e : x ≡ y)
    (r : Condition s) {rest : Condition s} →
    Restructuring (l & r) rest →
    Restructuring (l & v ↦ x ⨾ r) (v ↦ y ⨾ rest)
[ l ]&[ v ]↦[ refl ]⨾[ r ]⨾⨾ p = [ l ]&[ v ]⨾[ r ]⨾⨾ p

[_]↦[_]∎ : ∀ {s : StateThread} (v : Ref s) {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → Restructuring (v ↦ x ⨾ 𝟏) (v ↦ y ⨾ 𝟏)
[_]↦[_]∎ = [ 𝟏 ]&[_]↦[_]⨾[ 𝟏 ]⨾⨾ ∎

infixr -1 [_]&[_]&[_]⨾⨾_
[_]&[_]&[_]⨾⨾_ :
  {s : StateThread} (l m r : Condition s) {rest : Condition s} →
  Restructuring (l & r) rest →
  Restructuring (l & m & r) (m & rest)
[ l ]&[ 𝟏      ]&[ r ]⨾⨾ p = p
[ l ]&[ v ⨾⨾ m ]&[ r ]⨾⨾ p = [ l ]&[ v ]⨾[ m & r ]⨾⨾ [ l ]&[ m ]&[ r ]⨾⨾ p
