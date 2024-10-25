{-# OPTIONS --safe #-}
module Imperative.Lemmas where

open import Agda.Primitive
open import Data.List hiding ([_])
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.AllPairs hiding (module AllPairs)
open import Data.Product
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

import Imperative

module Spec (StateThread : Setω₀) (Ref : StateThread → Set lzero) where
  open Imperative.Spec StateThread Ref

  liveRefs& : {s : StateThread} (xs : Condition s) (ys : Condition s) → liveRefs (xs & ys) ≡ liveRefs xs ++ liveRefs ys
  liveRefs& 𝟏         ys = refl
  liveRefs& (x ⨾⨾ xs) ys = cong (x ∷_) (liveRefs& xs ys)

  infixr -1 [_]&[_]&[_]⨾⨾_
  [_]&[_]&[_]⨾⨾_ :
    {s : StateThread} (l m r : Condition s) {rest : Condition s} →
    Restructuring (l & r) rest →
    Restructuring (l & m & r) (m & rest)
  [ l ]&[ 𝟏      ]&[ r ]⨾⨾ p = p
  [ l ]&[ v ⨾⨾ m ]&[ r ]⨾⨾ p = [ l ]&[ v ]⨾[ m & r ]⨾⨾ [ l ]&[ m ]&[ r ]⨾⨾ p
  [_]∎ : {s : StateThread} (c : Condition s) → Restructuring c c
  [ 𝟏      ]∎ = ∎
  [ v ⨾⨾ c ]∎ = [ 𝟏 ]&[ v ]⨾[ c ]⨾⨾ [ c ]∎

  discards : {s : StateThread} {pre post : Condition s} → Restructuring pre post → Condition s
  discards [ discards ]╳           = discards
  discards ([ l ]&[ v ]⨾[ r ]⨾⨾ p) = discards p

  nondestructive :
    {s : StateThread} {pre post : Condition s} (p : Restructuring pre post) →
    Restructuring pre (post & discards p)
  nondestructive [ discards ]╳           = [ discards ]∎
  nondestructive ([ l ]&[ v ]⨾[ r ]⨾⨾ p) = [ l ]&[ v ]⨾[ r ]⨾⨾ nondestructive p

module ∈ {ℓ} {A : Set ℓ} where
  ++⁺ : {xs ys : List A} {x : A} → x ∈ xs ⊎ x ∈ ys → x ∈ xs ++ ys
  ++⁺ = [ ∈-++⁺ˡ , ∈-++⁺ʳ _ ]

module AllPairs {ℓA ℓR} {A : Set ℓA} {R : Rel A ℓR} where
  ++⁻ : {xs ys : List A} → AllPairs R (xs ++ ys) → AllPairs R xs × AllPairs R ys × All (λ x → All (R x) ys) xs
  ++⁻ {[]}     ps       = [] , ps , []
  ++⁻ {x ∷ xs} (p ∷ ps) =
    let l , r , lrs = ++⁻ ps in
    let ll , lr = All.++⁻ xs p in
    ll ∷ l , r , lr ∷ lrs
