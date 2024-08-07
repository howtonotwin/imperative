{-# OPTIONS --safe --lossy-unification #-}
module Imperative.Pure where

open import Agda.Primitive
open import Data.List as List hiding ([_])
open import Data.List.Membership.Propositional as ∈
open import Data.List.Membership.Propositional.Properties as ∈
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties as All
import Data.List.Relation.Unary.AllPairs as AllPairs
open import Data.List.Relation.Unary.AllPairs.Properties as AllPairs
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.Unique.Propositional as Unique
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.List.Extrema ≤-totalOrder
open import Data.Product
open import Data.Sum as ⊎
open import Data.Unit
open import Function
open import Level hiding (suc)
open import Relation.Binary.PropositionalEquality hiding ([_])

import Imperative
import Imperative.Lemmas as Lemmas
open import Realizer

private
  module @0 PureImpl where
    record StateThread : SSetω₀ where
    Ref : StateThread → Set lzero
    Ref _ = ℕ
    open Imperative.Spec StateThread Ref
    open Lemmas.Spec StateThread Ref

    Program :
      ∀ {ℓA ℓpre ℓpost} (s : StateThread) (A : Set ℓA)
      (@0 pre : Condition s ℓpre) (@0 post : A → Condition s ℓpost) → Set (ℓA ⊔ ℓpre ⊔ ℓpost)
    Program {ℓA} {ℓpre} {ℓpost} _ A pre post =
      (brk : ℕ) →
      Unique (liveRefs pre) → All (_< brk) (liveRefs pre) →
      Lift (ℓA ⊔ ℓpre ⊔ ℓpost)
        (Σ[ x ∈ A ]
        Unique (liveRefs (post x)) × All (λ r → r ∈ liveRefs pre ⊎ brk ≤ r) (liveRefs (post x)))

    runProgram :
      ∀ {ℓA ℓpost} {A : Set ℓA} {@0 post : (s : StateThread) → A → Condition s ℓpost} →
      ({s : StateThread} → Program s A 𝟏 (post s)) → A
    runProgram x = x 0 [] [] .lower .proj₁

    return :
      ∀ {s : StateThread} {ℓA ℓcond} {A : Set ℓA} {@0 cond : A → Condition s ℓcond}
      (x : A) → Program s A (cond x) cond
    return x brk sep alloced .lower = x , sep , All.tabulate inj₁

    _>>=_ :
      ∀ {s : StateThread} {ℓA ℓB ℓpre ℓmid ℓpost} {A : Set ℓA} {B : Set ℓB}
      {@0 pre : Condition s ℓpre} {@0 mid : A → Condition s ℓmid} {@0 post : B → Condition s ℓpost} →
      Program s A pre mid → ((x : A) → Program s B (mid x) post) → Program s B pre post
    _>>=_ {mid = mid} p q brk₁ sep₁ alloced₁ .lower =
      let lift (x , sep₂ , alloced₂) = p brk₁ sep₁ alloced₁ in
      let brk₂ = max brk₁ (List.map suc (liveRefs (mid x))) in
      let lift (y , sep₃ , alloced₃) = q x brk₂ sep₂ (All.map⁻ (xs≤max brk₁ _)) in
      y , sep₃ , All.map [ All.lookup alloced₂ , inj₂ ∘ ≤-trans (⊥≤max brk₁ _) ] alloced₃

    read :
      ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 x : A}
      (r : Ref s) → Program s (Realizer x) (r ↦ x ⨾ 𝟏) (λ _ → r ↦ x ⨾ 𝟏)
    read {x = x} r brk sep alloced .lower = realized x , sep , inj₁ (here refl) ∷ []

    write :
      ∀ {s : StateThread} {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {@0 x : A}
      (r : Ref s) (y : B) → Program s ⊤ (r ↦ x ⨾ 𝟏) (λ _ → r ↦ y ⨾ 𝟏)
    write r y brk sep alloced .lower = tt , sep , inj₁ (here refl) ∷ []

    alloc : {s : StateThread} → Program s (Ref s) 𝟏 (λ r → r ↦ tt ⨾ 𝟏)
    alloc brk sep alloced .lower = brk , [] ∷ [] , inj₂ ≤-refl ∷ []

    frame :
      ∀ {s : StateThread} {ℓA ℓpre ℓpost ℓside} {A : Set ℓA}
      (@0 side : Condition s ℓside) {@0 pre : Condition s ℓpre} {@0 post : A → Condition s ℓpost} →
      Program s A pre post → Program s A (side & pre) (λ x → side & post x)
    frame side {pre} {post} p brk sep alloced .lower =
      let sepₗ , sepᵣ , sepₗᵣ = Lemmas.AllPairs.++⁻ (subst Unique (liveRefs& side pre) sep) in
      let allocedₗ , allocedᵣ = All.++⁻ _ (subst (All (_< brk)) (liveRefs& side pre) alloced) in
      let lift (x , sep′ , alloced′) = p brk sepᵣ allocedᵣ in
      λ where
        .proj₁        → x
        .proj₂ .proj₁ →
          subst Unique (sym (liveRefs& side (post x)))
            (AllPairs.++⁺ sepₗ sep′
              (All.zipWith
                (λ (x∉pre , x<brk) → All.map [ All.lookup x∉pre , flip <-irrefl ∘ <-≤-trans x<brk ] alloced′)
                (sepₗᵣ , allocedₗ)))
        .proj₂ .proj₂ →
          subst (All _) (sym (liveRefs& side (post x)))
            (All.++⁺
              (All.tabulate (inj₁ ∘ subst (_ ∈_) (sym (liveRefs& side pre)) ∘ ∈.∈-++⁺ˡ))
              (All.map (⊎.map₁ (subst (_ ∈_) (sym (liveRefs& side pre)) ∘ ∈.∈-++⁺ʳ _)) alloced′))

    restructure :
      ∀ {s : StateThread} {ℓpre ℓpost} {@0 pre : Condition s ℓpre} {@0 post : Condition s ℓpost} →
      @0 Restructuring pre post → Program s ⊤ pre (λ _ → post)
    restructure ∎                              brk sep alloced .lower = tt , [] , []
    restructure ([ l ]&[ v ]↦[ _ ]⨾[ r ]⨾⨾ rs) brk sep alloced .lower =
      let sepₗ , sepᵥᵣ , sepₗ,ᵥᵣ = Lemmas.AllPairs.++⁻ (subst Unique (liveRefs& l (v ⨾⨾ r)) sep) in
      let sepᵥ,ᵣ , sepᵣ = AllPairs.uncons sepᵥᵣ in
      let sepᵥ,ₗ , sepₗ,ᵣ = All.unzipWith All.uncons sepₗ,ᵥᵣ in
      let sepₗᵣ = subst Unique (sym (liveRefs& l r)) (AllPairs.++⁺ sepₗ sepᵣ sepₗ,ᵣ) in
      let sepᵥ,ₗᵣ = subst (All _) (sym (liveRefs& l r)) (All.++⁺ (All.map (_∘ sym) sepᵥ,ₗ) sepᵥ,ᵣ) in
      let allocedₗ , allocedᵥᵣ = All.++⁻ _ (subst (All (_< brk)) (liveRefs& l (v ⨾⨾ r)) alloced) in
      let allocedᵥ , allocedᵣ = All.uncons allocedᵥᵣ in
      let allocedₗᵣ = subst (All (_< brk)) (sym (liveRefs& l r)) (All.++⁺ allocedₗ allocedᵣ) in
      let lift (tt , sep′ , alloced′) = restructure rs brk sepₗᵣ allocedₗᵣ in
      λ where
        .proj₁        → tt
        .proj₂ .proj₁ →
          All.map [ All.lookup sepᵥ,ₗᵣ , flip <-irrefl ∘ <-≤-trans allocedᵥ ] alloced′ ∷ sep′
        .proj₂ .proj₂ →
          _∷_
          (inj₁ (subst (_ ∈_) (sym (liveRefs& l (v ⨾⨾ r))) (∈-++⁺ʳ _ (here refl))))
          (All.map
            (⊎.map₁
              ( subst (_ ∈_) (sym (liveRefs& l (v ⨾⨾ r))) ∘
                Lemmas.∈.++⁺ ∘
                ⊎.map₂ there ∘
                ∈.∈-++⁻ _ ∘
                subst (_ ∈_) (liveRefs& l r)))
            alloced′)

@0 Pure : Imperative.Impl
Pure = record { PureImpl }

module @0 Pure = Imperative.Impl Pure
