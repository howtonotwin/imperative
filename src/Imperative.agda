{-# OPTIONS --safe #-}
module Imperative where

open import Agda.Primitive
open import Data.List
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Erased
open import Realizer

module Spec (StateThread : SSetω₀) (Ref : StateThread → Set lzero) where
  infix 1 _↦_
  record Assignment (s : StateThread) : SSetω₀ where
    constructor _↦_
    field
      var : Ref s
      {contentLevel} : Level
      {contentType} : Set contentLevel
      content : contentType

  infixr 0 _⨾_
  data Condition (s : StateThread) : SSetω₀ where
    𝟏   : Condition s
    _⨾_ : Assignment s → Condition s → Condition s
  infixr 0 _⨾⨾_
  pattern _⨾⨾_ v r = v ↦ _ ⨾ r

  liveRefs : {s : StateThread} → Condition s → List (Ref s)
  liveRefs 𝟏         = []
  liveRefs (x ⨾⨾ xs) = x ∷ liveRefs xs

  infixr 0 _&_
  _&_ : {s : StateThread} → Condition s → Condition s → Condition s
  𝟏        & ys = ys
  (x ⨾ xs) & ys = x ⨾ xs & ys

  infixr -1 [_]&[_]↦[_]⨾[_]⨾⨾_
  data Restructuring {s : StateThread} : Condition s → Condition s → SSetω₀ where
    ∎ : {discard : Condition s} → Restructuring discard 𝟏
    [_]&[_]↦[_]⨾[_]⨾⨾_ :
      ∀ {ℓ}
      (l : Condition s)
      (v : Ref s) {A : Set ℓ} {x y : A} (e : x ≡ y)
      (r : Condition s) {rest : Condition s} →
      Restructuring (l & r) rest →
      Restructuring (l & v ↦ x ⨾ r) (v ↦ y ⨾ rest)
  infixr -1 [_]&[_]⨾[_]⨾⨾_
  pattern [_]&[_]⨾[_]⨾⨾_ l v r p = [_]&[_]↦[_]⨾[_]⨾⨾_ l v refl r p

record Impl : SSetω₁ where
  field
    StateThread : SSetω₀
    Ref : StateThread → Set lzero
  open Spec StateThread Ref public
  field
    Program : ∀ {ℓ} (s : StateThread) (A : Set ℓ) (@0 pre : Condition s) (@0 post : A → Condition s) → Set ℓ
    runProgram :
      ∀ {ℓ} {A : Set ℓ} {@0 post : (s : StateThread) → A → Condition s} →
      ({s : StateThread} → Program s A 𝟏 (post s)) → A
    return :
      ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 cond : A → Condition s}
      (x : A) → Program s A (cond x) cond
    _>>=_ :
      ∀ {s : StateThread} {ℓA ℓB} {A : Set ℓA} {B : Set ℓB}
      {@0 pre : Condition s} {@0 mid : A → Condition s} {@0 post : B → Condition s} →
      Program s A pre mid → ((x : A) → Program s B (mid x) post) → Program s B pre post
    read :
      ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 x : A}
      (r : Ref s) → Program s (Realizer x) (r ↦ x ⨾ 𝟏) (λ _ → r ↦ x ⨾ 𝟏)
    write :
      ∀ {s : StateThread} {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} {@0 x : A}
      (r : Ref s) (y : B) → Program s ⊤ (r ↦ x ⨾ 𝟏) (λ _ → r ↦ y ⨾ 𝟏)
    alloc : {s : StateThread} → Program s (Ref s) 𝟏 (λ r → r ↦ tt ⨾ 𝟏)
    frame :
      ∀ {s : StateThread} {ℓ} {A : Set ℓ}
      (@0 side : Condition s) {@0 pre : Condition s} {@0 post : A → Condition s} →
      Program s A pre post → Program s A (side & pre) (λ x → side & post x)
    restructure :
      {s : StateThread} {@0 pre post : Condition s} →
      @0 Restructuring pre post → Program s ⊤ pre (λ _ → post)
    separate : {s : StateThread} {@0 cond : Condition s} → Program s (Erased (Unique (liveRefs cond))) cond (λ _ → cond)
  _>>_ :
      ∀ {s : StateThread} {ℓA ℓB} {A : Set ℓA} {B : Set ℓB}
      {@0 pre : Condition s} {@0 mid : A → Condition s} {@0 post : B → Condition s} →
      Program s A pre mid → ({x : A} → Program s B (mid x) post) → Program s B pre post
  p₁ >> p₂ = do
    x ← p₁
    p₂ {x}
  writeRealized :
    ∀ {s : StateThread} {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} {@0 x : A} {@0 y : B}
    (r : Ref s) → Realizer y → Program s ⊤ (r ↦ x ⨾ 𝟏) (λ _ → r ↦ y ⨾ 𝟏)
  writeRealized r (realized y) = write r y
  init : ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 x : A} → Realizer x → Program s (Ref s) 𝟏 (λ r → r ↦ x ⨾ 𝟏)
  init x = do
    v ← alloc
    writeRealized v x
    return v
