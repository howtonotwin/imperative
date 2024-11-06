{-# OPTIONS --safe #-}
module Imperative where

open import Agda.Primitive
open import Data.List
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.Nat
open import Data.Nat.Properties
open import Data.Unit
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality

open import ArrayValue
open import Erased
open import Realizer

import Imperative.Condition
import Imperative.Framing
import Imperative.Restructuring

record Impl : Setω₁ where
  field
    StateThread : Setω₀
    Array : StateThread → @0 ℕ → Set lzero
  module Condition = Imperative.Condition StateThread Array
  module Restructuring = Imperative.Restructuring StateThread Array
  module Framing = Imperative.Framing StateThread Array
  open Condition
  open Restructuring
  open Framing
  field
    Program : ∀ {ℓ} (s : StateThread) (A : Set ℓ) (@0 pre : Condition s) (@0 post : A → Condition s) → Set ℓ
    runProgram :
      ∀ {ℓ} {A : Set ℓ} →
      ({s : StateThread} → Program s A 𝟏 (λ _ → 𝟏)) → A
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
      ∀ {s : StateThread} {@0 ℓA} {ℓB} {@0 A : Set ℓA} {B : Set ℓB} {@0 x : A}
      (r : Ref s) (y : B) → Program s ⊤ (r ↦ x ⨾ 𝟏) (λ _ → r ↦ y ⨾ 𝟏)
    allocArray :
      {s : StateThread} (n : ℕ) →
      Program s (Array s n) 𝟏 (λ r → fullSlice r ↦＊ ArrayValue.replicate n tt)
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
  p >> q = do
    x ← p
    q {x}
  writeRealized :
    ∀ {s : StateThread} {@0 ℓA} {ℓB} {@0 A : Set ℓA} {B : Set ℓB} {@0 x : A} {@0 y : B}
    (r : Ref s) → Realizer y → Program s ⊤ (r ↦ x ⨾ 𝟏) (λ _ → r ↦ y ⨾ 𝟏)
  writeRealized r (realized y) = write r y
  alloc : {s : StateThread} → Program s (Ref s) 𝟏 (λ r → r ↦ tt ⨾ 𝟏)
  alloc = do
    a ← allocArray 1
    return (fullSlice a)
  init : ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 x : A} → Realizer x → Program s (Ref s) 𝟏 (λ r → r ↦ x ⨾ 𝟏)
  init x = do
    v ← alloc
    writeRealized v x
    return v
  writeSlice :
    {s : StateThread} {@0 n : ℕ} {@0 pre : ArrayValue n} (arr : Slice s n) (xs : ArrayValue n) →
    Program s ⊤ (arr ↦＊ pre) (λ _ → arr ↦＊ xs)
  writeSlice {pre = []}      arr []       = return tt
  writeSlice {pre = p ∷ pre} arr (x ∷ xs) = do
    frame (++ arr ↦＊ _) (write (* arr) x)
    restructure (unfocus (((* arr ⨾⨾ 𝟏) &> >[ ++ arr ↦＊ _ ]<) <&> >[ * arr ⨾⨾ 𝟏 ]<))
    frame (* arr ⨾⨾ 𝟏) (writeSlice (++ arr) xs)
    restructure (unfocus (((++ arr ↦＊ _) &> >[ * arr ⨾⨾ 𝟏 ]<) <&> (>[ ++ arr ↦＊ _ ]< <& 𝟏)))
  readVec :
    ∀ {s : StateThread} {ℓ} {A : Set ℓ} {n : ℕ} (arr : Slice s n) {@0 xs : Vec A n} →
    Program s (Realizer xs) (arr ↦＊ vec xs) (λ _ → arr ↦＊ vec xs)
  readVec {n = zero}  arr {xs = []}     = return (realized [])
  readVec {n = suc n} arr {xs = x ∷ xs} = do
    realized .x ← frame (++ arr ↦＊ _) (read (* arr))
    restructure (unfocus (((* arr ⨾⨾ 𝟏) &> >[ ++ arr ↦＊ _ ]<) <&> >[ * arr ⨾⨾ 𝟏 ]<))
    realized .xs ← frame (* arr ⨾⨾ 𝟏) (readVec (++ arr))
    restructure (unfocus (((++ arr ↦＊ _) &> >[ * arr ⨾⨾ 𝟏 ]<) <&> (>[ ++ arr ↦＊ _ ]< <& 𝟏)))
    return (realized (x ∷ xs))
