{-# OPTIONS --safe #-}
module Imperative where

open import Agda.Primitive
open import Data.List
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.Nat
open import Data.Nat.Properties
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Erased
open import Realizer
import ArrayValue as SpecArrayValue

module Spec (StateThread : Setω₀) (Ref : StateThread → Set lzero) where
  infix 1 _↦_
  record Assignment (s : StateThread) : Setω₀ where
    constructor _↦_
    field
      var : Ref s
      {contentLevel} : Level
      {contentType} : Set contentLevel
      content : contentType

  infixr 0 _⨾_
  data Condition (s : StateThread) : Setω₀ where
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

  Array : StateThread → ℕ → Set lzero
  Array s n = (i : ℕ) → .(i < n) → Ref s
  module ArrayValue = SpecArrayValue
  open ArrayValue using (ArrayValue; []; _∷_) public
  infix 1 _↦＊_
  _↦＊_ : {s : StateThread} {n : ℕ} → Array s n → ArrayValue n → Condition s
  f ↦＊ []     = 𝟏
  f ↦＊ x ∷ xs = f zero z<s ↦ x ⨾ (λ i i<n → f (suc i) (s<s i<n)) ↦＊ xs

  infixr -1 [_]&[_]⨾[_]⨾⨾_
  data Restructuring {s : StateThread} : Condition s → Condition s → Setω₀ where
    ∎ : {discards : Condition s} → Restructuring discards 𝟏
    [_]&[_]⨾[_]⨾⨾_ :
      ∀ (l : Condition s)
      (v : Ref s) {ℓ} {A : Set ℓ} {x : A}
      (r : Condition s) {rest : Condition s} →
      Restructuring (l & r) rest →
      Restructuring (l & v ↦ x ⨾ r) (v ↦ x ⨾ rest)
  infixr -1 [_]&[_]↦[_]⨾[_]⨾⨾_
  [_]&[_]↦[_]⨾[_]⨾⨾_ :
      ∀ {s : StateThread}
      (l : Condition s)
      (v : Ref s) {ℓ} {A : Set ℓ} {x y : A} (e : x ≡ y)
      (r : Condition s) {rest : Condition s} →
      Restructuring (l & r) rest →
      Restructuring (l & v ↦ x ⨾ r) (v ↦ y ⨾ rest)
  [ l ]&[ v ]↦[ refl ]⨾[ r ]⨾⨾ p = [ l ]&[ v ]⨾[ r ]⨾⨾ p
  infixr -1 [_]&[_]&[_]⨾⨾_
  [_]&[_]&[_]⨾⨾_ :
    {s : StateThread} (l m r : Condition s) {rest : Condition s} →
    Restructuring (l & r) rest →
    Restructuring (l & m & r) (m & rest)
  [ l ]&[ 𝟏         ]&[ r ]⨾⨾ p = p
  [ l ]&[ v ↦ _ ⨾ m ]&[ r ]⨾⨾ p = [ l ]&[ v ]⨾[ m & r ]⨾⨾ [ l ]&[ m ]&[ r ]⨾⨾ p
  [_]∎ : {s : StateThread} (c : Condition s) → Restructuring c c
  [ 𝟏         ]∎ = ∎
  [ v ↦ _ ⨾ c ]∎ = [ 𝟏 ]&[ v ]⨾[ c ]⨾⨾ [ c ]∎

  discards : {s : StateThread} {pre post : Condition s} → Restructuring pre post → Condition s
  discards (∎ {discards = discards}) = discards
  discards ([ l ]&[ v ]⨾[ r ]⨾⨾ p)   = discards p

  nondestructive :
    {s : StateThread} {pre post : Condition s} (p : Restructuring pre post) →
    Restructuring pre (post & discards p)
  nondestructive ∎                       = [ _ ]∎
  nondestructive ([ l ]&[ v ]⨾[ r ]⨾⨾ p) = [ l ]&[ v ]⨾[ r ]⨾⨾ nondestructive p

record Impl : Setω₁ where
  field
    StateThread : Setω₀
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
    allocArray :
      {s : StateThread} (n : ℕ) →
      Program s (Array s n) 𝟏 (λ r → r ↦＊ ArrayValue.replicate n tt)
    frame :
      ∀ {s : StateThread} {ℓ} {A : Set ℓ}
      (@0 side : Condition s) {@0 pre : Condition s} {@0 post : A → Condition s} →
      Program s A pre post → Program s A (pre & side) (λ x → post x & side)
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
  alloc : {s : StateThread} → Program s (Ref s) 𝟏 (λ r → r ↦ tt ⨾ 𝟏)
  alloc = do
    rs ← allocArray 1
    return (rs 0 _)
  init : ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 x : A} → Realizer x → Program s (Ref s) 𝟏 (λ r → r ↦ x ⨾ 𝟏)
  init x = do
    v ← alloc
    writeRealized v x
    return v
  reframe :
    ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 pre focus : Condition s} {@0 post : A → Condition s}
    (@0 r : Restructuring pre focus) → Program s A focus post → Program s A pre (λ x → post x & discards r)
  reframe r p = do
    restructure (nondestructive r)
    frame (discards r) p
