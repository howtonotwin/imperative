{-# OPTIONS --safe #-}
module Imperative.Framing where

open import Agda.Primitive
open import Data.Nat

open import LargeEq

open import Imperative.Condition
open import Imperative.Restructuring

module _ {Ref : Set lzero} where
  data Framing (outer inner : Condition Ref) : Condition Ref → Setω₀ where
    focus : (p : Restructuring outer inner) → Framing outer inner (discards p)
  unfocus : {o i d : Condition Ref} → Framing o i d → Restructuring o i
  unfocus (focus p) = p

  substFraming : {o₁ o₂ i d : Condition Ref} → o₁ ≡ω₀ o₂ → Framing o₁ i d → Framing o₂ i d
  substFraming reflω₀ p = p

  >[_]╳< : (d : Condition Ref) → Framing d 𝟏 d
  >[ d ]╳< = focus [ d ]╳

  infixr -1 >[_]&[_]⨾[_]⨾⨾>_
  >[_]&[_]⨾[_]⨾⨾>_ :
    ∀ (l : Condition Ref)
    (v : Ref) {ℓ} {A : Set ℓ} {x : A}
    (r : Condition Ref) {f d : Condition Ref} →
    Framing (l & r) f d →
    Framing (l & v ↦ x ⨾ r) (v ↦ x ⨾ f) d
  >[ l ]&[ v ]⨾[ r ]⨾⨾> focus p = focus ([ l ]&[ v ]⨾[ r ]⨾⨾ p)

  infixr 0 _&>_
  _&>_ : {r f d : Condition Ref} (l : Condition Ref) → Framing r f d → Framing (l & r) f (l & d)
  l &> focus [ discards ]╳           = >[ l & discards ]╳<
  l &> focus ([ m ]&[ v ]⨾[ r ]⨾⨾ p) =
      substFraming (assoc& l m (v ⨾⨾ r))
        (>[ l & m ]&[ v ]⨾[ r ]⨾⨾> substFraming (symω₀ (assoc& l m r)) (l &> focus p))
  infixl 0 _<&_
  _<&_ : {l f d : Condition Ref} → Framing l f d → (r : Condition Ref) → Framing (l & r) f (d & r)
  focus [ discards ]╳           <& r = >[ discards & r ]╳<
  focus ([ l ]&[ v ]⨾[ m ]⨾⨾ p) <& r =
    substFraming (symω₀ (assoc& l (v ⨾⨾ m) r))
      (>[ l ]&[ v ]⨾[ m & r ]⨾⨾> substFraming (assoc& l m r) (focus p <& r))

  >[_]< : (cond : Condition Ref) → Framing cond cond 𝟏
  >[ 𝟏         ]< = >[ 𝟏 ]╳<
  >[ v ⨾⨾ cond ]< = >[ 𝟏 ]&[ v ]⨾[ cond ]⨾⨾> >[ cond ]<
  >𝟏< : {cond : Condition Ref} → Framing cond 𝟏 cond
  >𝟏< = >[ _ ]╳<
  >[!_!]< : {pre post : Condition Ref} → pre ≡ω₀ post → Framing pre post 𝟏
  >[! reflω₀ !]< = >[ _ ]<

  infixr 1 _<&>_
  _<&>_ :
    {outer first middle second side : Condition Ref} →
    Framing outer first middle → Framing middle second side → Framing outer (first & second) side
  focus [ outer ]╳              <&> q = q
  focus ([ l ]&[ v ]⨾[ r ]⨾⨾ p) <&> q = >[ l ]&[ v ]⨾[ r ]⨾⨾> focus p <&> q

  cancelFraming : {o i d : Condition Ref} → Framing o i d → Restructuring o (i & d)
  cancelFraming (focus [ discards ]╳)           = unfocus >[ discards ]<
  cancelFraming (focus ([ l ]&[ v ]⨾[ r ]⨾⨾ p)) = [ l ]&[ v ]⨾[ r ]⨾⨾ cancelFraming (focus p)
