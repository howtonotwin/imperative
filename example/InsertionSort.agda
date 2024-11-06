{-# OPTIONS --safe #-}
module InsertionSort where

open import Function
open import Data.Maybe hiding (_>>=_)
open import Data.Maybe.Relation.Binary.Connected hiding (refl; sym)
open import Data.Nat
open import Data.Nat.Properties
open import Data.List as List
import Data.List.Properties as List
open import Data.List.Relation.Unary.Linked
open import Data.List.Relation.Unary.Sorted.TotalOrder ≤-totalOrder
import Data.List.Relation.Unary.Sorted.TotalOrder.Properties as Sorted
open import Data.Product
open import Data.Sum
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as Vec
open import Relation.Binary.PropositionalEquality renaming (trans to infixl 1 _∙_)
open import Relation.Nullary.Decidable

open import ArrayValue
open import Erased
open import LargeEq
open import Realizer

import Imperative
import Imperative.ManualStyle

import Logic.Lemmas as Lemmas
open import Logic.Permutation

module _ (I : Imperative.Impl) where
  open Imperative.ManualStyle I

  insert :
    {s : StateThread} (n : ℕ) (arr : Slice s (suc n)) (@0 pre : Vec ℕ n) (x : ℕ) {@0 z : ℕ} →
    @0 Sorted (Vec.toList pre) →
    Program s
      (Erased (Σ[ post ∈ Vec ℕ (suc n) ] Insertion x pre post × Sorted (Vec.toList post)))
      (arr ↦＊ vec (pre Vec.∷ʳ z))
      λ (erased (post , _)) → arr ↦＊ vec post
  insert zero    arr []              x p = do
    write (* arr) x
    return (erased (x ∷ [] , here , [-]))
  insert (suc n) arr pre             x p with erased (Vec.initLast pre)
  insert (suc n) arr .(pre Vec.∷ʳ y) x p | erased (pre , y , refl) = do
    restructure [! congω₀ (arr ↦＊_) (vec-∷ʳ _ _) ∙ω₀ ↦＊-∷ʳ arr _ _ !]∎
    realized .y ← frame (>[ arr [∶-1] ↦＊ _ ]< <& (arr [-1] ⨾⨾ 𝟏)) do
      restructure [! congω₀ (arr [∶-1] ↦＊_) (vec-∷ʳ _ _) ∙ω₀ ↦＊-∷ʳ (arr [∶-1]) _ _ !]∎
      y′ ← frame ((arr [∶-1] [∶-1] ↦＊ _) &> >[ arr [∶-1] [-1] ⨾⨾ 𝟏 ]<) (read (arr [∶-1] [-1]))
      restructure (unfocus (
            ((arr [∶-1] [-1] ⨾⨾ 𝟏) &> (>[ arr [∶-1] [∶-1] ↦＊ _ ]< <& 𝟏))
        <&> >[ arr [∶-1] [-1] ⨾⨾ 𝟏 ]<))
      restructure [! symω₀ (congω₀ (arr [∶-1] ↦＊_) (vec-∷ʳ _ _) ∙ω₀ ↦＊-∷ʳ (arr [∶-1]) _ _) !]∎
      return y′
    case y ≤? x of λ where
      (yes y≤x) → do
        frame ((arr [∶-1] ↦＊ _) &> >[ arr [-1] ⨾⨾ 𝟏 ]<) (write (arr [-1]) x)
        restructure (unfocus (((arr [-1] ⨾⨾ 𝟏) &> (>[ arr [∶-1] ↦＊ _ ]< <& 𝟏)) <&> >[ arr [-1] ⨾⨾ 𝟏 ]<))
        restructure [! symω₀ (congω₀ (arr ↦＊_) (vec-∷ʳ _ _) ∙ω₀ ↦＊-∷ʳ arr _ _) !]∎
        return (erased (
          pre Vec.∷ʳ y Vec.∷ʳ x ,
          ereh ,
          subst Sorted
            (sym (Lemmas.Vec.toList-∷ʳ (pre Vec.∷ʳ y) x))
            (Sorted.++⁺ ≤-totalOrder
              p
              (subst (λ y → Connected _≤_ y (just x))
                (sym (cong List.last (Lemmas.Vec.toList-∷ʳ pre y) ∙ Lemmas.List.last-∷ʳ (Vec.toList pre) y))
                (just y≤x))
              [-])))
      (no  y≰x) → do
        frame ((arr [∶-1] ↦＊ _) &> >[ arr [-1] ⨾⨾ 𝟏 ]<) (write (arr [-1]) y)
        erased (post , i , sorted) ←
          frame ((arr [-1] ⨾⨾ 𝟏) &> (>[ arr [∶-1] ↦＊ _ ]< <& 𝟏))
            (insert n (arr [∶-1]) pre x (Lemmas.Sorted.++⁻ (subst Sorted (Lemmas.Vec.toList-∷ʳ pre y) p) .proj₁))
        restructure [! symω₀ (congω₀ (arr ↦＊_) (vec-∷ʳ _ _) ∙ω₀ ↦＊-∷ʳ arr _ _) !]∎
        return (erased (
          post Vec.∷ʳ y ,
          ereht i ,
          subst Sorted
            (sym (Lemmas.Vec.toList-∷ʳ post y))
            (Sorted.++⁺ ≤-totalOrder
              sorted
              (case last-Insertion i of λ @0 where
                (inj₁ e) → subst (λ x′ → Connected _≤_ x′ (just y)) (sym e) (just (≰⇒≥ y≰x))
                (inj₂ e) →
                  subst (λ x′ → Connected _≤_ x′ (just y))
                    (sym e)
                    (Lemmas.Sorted.++⁻ (subst Sorted (Lemmas.Vec.toList-∷ʳ pre y) p) .proj₂ .proj₁))
              [-])))

  insertionSort :
    {s : StateThread} (i m : ℕ) (let n = i + m) (arr : Slice s n) (@0 sorted : Vec ℕ i) (@0 unsorted : Vec ℕ m) →
    @0 Sorted (Vec.toList sorted) →
    Program s
      (Erased (Σ[ out ∈ Vec ℕ n ] Permutation (sorted Vec.++ unsorted) out × Sorted (Vec.toList out)))
      (arr ↦＊ vec (sorted Vec.++ unsorted))
      λ (erased (out , _)) → arr ↦＊ vec out
  insertionSort i zero    arr sorted []       p =
    return (erased (
      sorted Vec.++ [] ,
      Permutation-refl ,
      subst Sorted
        (sym (Vec.toList-++ sorted [] ∙ List.++-identityʳ (Vec.toList sorted)))
        p))
  insertionSort i (suc m) arr sorted (x ∷ xs) isSorted = do
    let module Halves = ↦＊-++ i (suc m) arr
    let eqn = +-suc i m
    let arr′ = substSlice eqn arr
    let module Halves′ = ↦＊-++ (suc i) m arr′
    restructure [! congω₀ (arr ↦＊_) (vec-++ sorted (x ∷ xs)) ∙ω₀ Halves.eqn (vec sorted) (vec (x ∷ xs)) !]∎
    realized .x ←
      frame
        ((Halves.left ↦＊ _) &> (>[ * Halves.right ⨾⨾ 𝟏 ]< <& (++ Halves.right ↦＊ _)))
        (read (* Halves.right))
    erased (sorted₁ , x∈sorted₁ , isSorted₁) ← frame
      (    ((* Halves.right ⨾⨾ 𝟏) &> (>[ Halves.left ↦＊ _ ]< <& (++ Halves.right ↦＊ _)))
       <&> (>[ * Halves.right ⨾⨾ 𝟏 ]< <& (++ Halves.right ↦＊ _)))
      do
        restructure [! symω₀ (congω₀ (Halves′.left ↦＊_) (vec-∷ʳ _ _) ∙ω₀ ↦＊-∷ʳ Halves′.left _ _) !]∎
        insert i Halves′.left sorted x isSorted
    restructure [! symω₀ (congω₀ (arr′ ↦＊_) (vec-++ _ xs) ∙ω₀ Halves′.eqn (vec _) (vec xs)) !]∎
    erased (sorted₂ , sorting , isSorted₂) ← insertionSort (suc i) m arr′ sorted₁ xs isSorted₁
    restructure [! substSlice-↦＊-cast eqn arr _ ∙ω₀ congω₀ (arr ↦＊_) (symω₀ (vec-cast (sym eqn) _)) !]∎
    return (erased (
      Vec.cast _ sorted₂ ,
      subst (λ v → Permutation v (Vec.cast (sym eqn) sorted₂))
        (Vec.∷ʳ-++-eqFree x sorted)
        (cast-Permutation (sym eqn)
          (Permutation-trans
            (++-Permutationˡ xs (Insertion-unique ereh x∈sorted₁))
            sorting)) ,
      subst Sorted (sym (Vec.toList-cast _ sorted₂)) isSorted₂))

  sorted : {n : ℕ} (xs : Vec ℕ n) → Σ[ ys ∈ Vec ℕ n ] Erased (Permutation xs ys × Sorted (Vec.toList ys))
  sorted xs = runProgram do
    arr ← allocArray _
    writeSlice (fullSlice arr) (vec xs)
    erased (xs′ , prf) ← insertionSort 0 _ (fullSlice arr) [] _ []
    realized .xs′ ← readVec (fullSlice arr)
    restructure [ fullSlice arr ↦＊ _ ]╳
    return (xs′ , erased prf)
