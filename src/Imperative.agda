{-# OPTIONS --safe #-}
module Imperative where

open import Agda.Primitive
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Realizer

module Spec (StateThread : SSetω₀) (Ref : StateThread → Set lzero) where
  infix 1 _↦_
  record Assignment (s : StateThread) (ℓ : Level) : SSet (lsuc ℓ) where
    constructor _↦_
    field
      var : Ref s
      {contentType} : Set ℓ
      content : contentType

  infixr 0 _⨾_
  data Condition (s : StateThread) : (ℓ : Level) → SSetω₀ where
    𝟏 : Condition s lzero
    _⨾_ : {ℓ₁ ℓ₂ : Level} → Assignment s ℓ₁ → Condition s ℓ₂ → Condition s (ℓ₁ ⊔ ℓ₂)

  infixr 0 _&_
  _&_ : {s : StateThread} {ℓ₁ ℓ₂ : Level} → Condition s ℓ₁ → Condition s ℓ₂ → Condition s (ℓ₁ ⊔ ℓ₂)
  𝟏        & ys = ys
  (x ⨾ xs) & ys = x ⨾ xs & ys

  infixr -1 [_]&[_]↦[_]⨾[_]⨾⨾_
  data Restructuring {s : StateThread} : {ℓ₁ ℓ₂ : Level} → Condition s ℓ₁ → Condition s ℓ₂ → SSetω₀ where
    ∎ : {ℓ : Level} {discard : Condition s ℓ} → Restructuring discard 𝟏
    [_]&[_]↦[_]⨾[_]⨾⨾_ :
      {ℓl ℓ ℓr ℓrest : Level}
      (l : Condition s ℓl)
      (v : Ref s) {A : Set ℓ} {x y : A} (e : x ≡ y)
      (r : Condition s ℓr)
      {rest : Condition s ℓrest} → Restructuring (l & r) rest →
      Restructuring (l & v ↦ x ⨾ r) (v ↦ y ⨾ rest)

  infixr 0 _⨾⨾_
  pattern _⨾⨾_ v r = v ↦ _ ⨾ r
  infixr -1 [_]&[_]⨾[_]⨾⨾_
  pattern [_]&[_]⨾[_]⨾⨾_ l v r p = [_]&[_]↦[_]⨾[_]⨾⨾_ l v refl r p

record Impl : SSetω₁ where
  field
    StateThread : SSetω₀
    Ref : StateThread → Set lzero
  open Spec StateThread Ref public
  field
    Program :
      ∀ {ℓA ℓpre ℓpost} (s : StateThread) (A : Set ℓA)
      (@0 pre : Condition s ℓpre) (@0 post : A → Condition s ℓpost) → Set (ℓA ⊔ ℓpre ⊔ ℓpost)
    runProgram :
      ∀ {ℓA ℓpost} {A : Set ℓA} {@0 post : (s : StateThread) → A → Condition s ℓpost} →
      ({s : StateThread} → Program s A 𝟏 (post s)) → A
    return :
      ∀ {s : StateThread} {ℓA ℓcond} {A : Set ℓA} {@0 cond : A → Condition s ℓcond}
      (x : A) → Program s A (cond x) cond
    _>>=_ :
      ∀ {s : StateThread} {ℓA ℓB ℓpre ℓmid ℓpost} {A : Set ℓA} {B : Set ℓB}
      {@0 pre : Condition s ℓpre} {@0 mid : A → Condition s ℓmid} {@0 post : B → Condition s ℓpost} →
      Program s A pre mid → ((x : A) → Program s B (mid x) post) → Program s B pre post
    read :
      ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 x : A}
      (r : Ref s) → Program s (Realizer x) (r ↦ x ⨾ 𝟏) (λ _ → r ↦ x ⨾ 𝟏)
    write :
      ∀ {s : StateThread} {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {@0 x : A}
      (r : Ref s) (y : B) → Program s ⊤ (r ↦ x ⨾ 𝟏) (λ _ → r ↦ y ⨾ 𝟏)
    alloc : {s : StateThread} → Program s (Ref s) 𝟏 (λ r → r ↦ tt ⨾ 𝟏)
    frame :
      ∀ {s : StateThread} {ℓA ℓpre ℓpost ℓside} {A : Set ℓA}
      (@0 side : Condition s ℓside) {@0 pre : Condition s ℓpre} {@0 post : A → Condition s ℓpost} →
      Program s A pre post → Program s A (side & pre) (λ x → side & post x)
    restructure :
      ∀ {s : StateThread} {ℓpre ℓpost} {@0 pre : Condition s ℓpre} {@0 post : Condition s ℓpost} →
      @0 Restructuring pre post → Program s ⊤ pre (λ _ → post)
  _>>_ :
      ∀ {s : StateThread} {ℓA ℓB ℓpre ℓmid ℓpost} {A : Set ℓA} {B : Set ℓB}
      {@0 pre : Condition s ℓpre} {@0 mid : A → Condition s ℓmid} {@0 post : B → Condition s ℓpost} →
      Program s A pre mid → ({x : A} → Program s B (mid x) post) → Program s B pre post
  p₁ >> p₂ = do
    x ← p₁
    p₂ {x}
  writeRealized :
    ∀ {s : StateThread} {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {@0 x : A} {@0 y : B}
    (r : Ref s) → Realizer y → Program s ⊤ (r ↦ x ⨾ 𝟏) (λ _ → r ↦ y ⨾ 𝟏)
  writeRealized r (realized y) = write r y
  init : ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 x : A} → Realizer x → Program s (Ref s) 𝟏 (λ r → r ↦ x ⨾ 𝟏)
  init x = do
    v ← alloc
    writeRealized v x
    return v
