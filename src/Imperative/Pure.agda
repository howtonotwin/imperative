{-# OPTIONS --safe --lossy-unification #-}
module Imperative.Pure where

open import Agda.Primitive
open import Data.List as List hiding ([_])
import Data.List.Properties as List
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
open import Relation.Binary.PropositionalEquality renaming (trans to infixl 1 _∙_) hiding ([_])

open import ArrayValue
open import Erased
open import Realizer

import Imperative
import Imperative.Condition
import Imperative.Restructuring
import Imperative.Lemmas as Lemmas

private
  module @0 PureImpl where
    record StateThread : Setω₀ where
    Array : StateThread → @0 ℕ → Set lzero
    Array _ _ = ℕ
    open Imperative.Condition StateThread Array
    open Imperative.Restructuring StateThread Array

    private
      lea : {s : StateThread} → Ref s → ℕ
      lea (slice a o _) = o + a
      liveAddrs : {s : StateThread} → Condition s → List ℕ
      liveAddrs c = List.map lea (liveRefs c)
      liveAddrs& : {s : StateThread} (c d : Condition s) → liveAddrs (c & d) ≡ liveAddrs c List.++ liveAddrs d
      liveAddrs& c d = cong (List.map lea) (liveRefs-& c d) ∙ List.map-++ lea _ _

    Program : ∀ {ℓ} (s : StateThread) (A : Set ℓ) (@0 pre : Condition s) (@0 post : A → Condition s) → Set ℓ
    Program _ A pre post =
      (brk : ℕ) → Unique (liveAddrs pre) → All (_< brk) (liveAddrs pre) →
      Σ[ x ∈ A ] Unique (liveAddrs (post x)) × All (λ r → r ∈ liveAddrs pre ⊎ brk ≤ r) (liveAddrs (post x))

    runProgram :
      ∀ {ℓ} {A : Set ℓ} →
      ({s : StateThread} → Program s A 𝟏 (λ _ → 𝟏)) → A
    runProgram x = x 0 [] [] .proj₁

    return :
      ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 cond : A → Condition s}
      (x : A) → Program s A (cond x) cond
    return x brk sep alloced = x , sep , All.tabulate inj₁

    _>>=_ :
      ∀ {s : StateThread} {ℓA ℓB} {A : Set ℓA} {B : Set ℓB}
      {@0 pre : Condition s} {@0 mid : A → Condition s} {@0 post : B → Condition s} →
      Program s A pre mid → ((x : A) → Program s B (mid x) post) → Program s B pre post
    _>>=_ {mid = mid} p q brk₁ sep₁ alloced₁ =
      let x , sep₂ , alloced₂ = p brk₁ sep₁ alloced₁ in
      let brk₂ = max brk₁ (List.map suc (liveAddrs (mid x))) in
      let y , sep₃ , alloced₃ = q x brk₂ sep₂ (All.map⁻ (xs≤max brk₁ _)) in
      y , sep₃ , All.map [ All.lookup alloced₂ , inj₂ ∘ ≤-trans (⊥≤max brk₁ _) ] alloced₃

    read :
      ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 x : A}
      (r : Ref s) → Program s (Realizer x) (r ↦ x ⨾ 𝟏) (λ _ → r ↦ x ⨾ 𝟏)
    read {x = x} r brk sep alloced = realized x , sep , inj₁ (here refl) ∷ []

    write :
      ∀ {s : StateThread} {@0 ℓA} {ℓB} {@0 A : Set ℓA} {B : Set ℓB} {@0 x : A}
      (r : Ref s) (y : B) → Program s ⊤ (r ↦ x ⨾ 𝟏) (λ _ → r ↦ y ⨾ 𝟏)
    write r y brk sep alloced = tt , sep , inj₁ (here refl) ∷ []

    frame :
      ∀ {s : StateThread} {ℓ} {A : Set ℓ}
      (@0 side : Condition s) {@0 pre : Condition s} {@0 post : A → Condition s} →
      Program s A pre post → Program s A (pre & side) (λ x → post x & side)
    frame side {pre} {post} p brk sep alloced =
      let sepₗ , sepᵣ , sepₗᵣ = Lemmas.AllPairs.++⁻ (subst Unique (liveAddrs& pre side) sep) in
      let allocedₗ , allocedᵣ = All.++⁻ _ (subst (All (_< brk)) (liveAddrs& pre side) alloced) in
      let x , sep′ , alloced′ = p brk sepₗ allocedₗ in
      λ where
        .proj₁        → x
        .proj₂ .proj₁ →
          subst Unique (sym (liveAddrs& (post x) side))
            (AllPairs.++⁺ sep′ sepᵣ
              (All.map
                [ All.lookup sepₗᵣ , (λ brk≤ → All.map (λ <brk n → <-irrefl (sym n) (<-≤-trans <brk brk≤)) allocedᵣ) ]
                alloced′))
        .proj₂ .proj₂ →
          subst (All _) (sym (liveAddrs& (post x) side))
            (All.++⁺
              (All.map (⊎.map₁ (subst (_ ∈_) (sym (liveAddrs& pre side)) ∘ ∈.∈-++⁺ˡ)) alloced′)
              (All.tabulate (inj₁ ∘ subst (_ ∈_) (sym (liveAddrs& pre side)) ∘ ∈.∈-++⁺ʳ _)))

    private
      enumFromFor : (n l : ℕ) → List ℕ
      enumFromFor n zero    = []
      enumFromFor n (suc l) = n ∷ enumFromFor (suc n) l
      ∈-enumFromFor : (n l : ℕ) {x : ℕ} → x ∈ enumFromFor n l → n ≤ x
      ∈-enumFromFor n (suc l) (here refl) = ≤-refl
      ∈-enumFromFor n (suc l) (there p)   = ≤-trans (n≤1+n n) (∈-enumFromFor (suc n) l p)
      Unique-enumFromFor : (n l : ℕ) → Unique (enumFromFor n l)
      Unique-enumFromFor n zero    = []
      Unique-enumFromFor n (suc l) =
        All.tabulate (λ { p refl → 1+n≰n (∈-enumFromFor (suc n) l p) }) ∷ Unique-enumFromFor (suc n) l
      liveRefsArray :
        (u i n a : ℕ) (p : i + n ≤ u) →
        liveAddrs (slice a i p ↦＊ ArrayValue.replicate n tt) ≡ enumFromFor (i + a) n
      liveRefsArray u i zero    a p = refl
      liveRefsArray u i (suc n) a p = cong (i + a ∷_) (liveRefsArray u (suc i) n a (subst (_≤ u) (+-suc i n) p))
    allocArray :
      {s : StateThread} (n : ℕ) → Program s (Array s n) 𝟏 (λ a → fullSlice a ↦＊ ArrayValue.replicate n tt)
    allocArray n brk sep alloced =
      let eqn = sym (liveRefsArray n 0 n brk ≤-refl) in
      brk , subst Unique eqn (Unique-enumFromFor brk n) , subst (All _) eqn (All.tabulate (inj₂ ∘ ∈-enumFromFor brk n))

    restructure :
      {s : StateThread} {@0 pre post : Condition s} →
      @0 Restructuring pre post → Program s ⊤ pre (λ _ → post)
    restructure ╳                        brk sep alloced = tt , [] , []
    restructure ([ l ]&[ v ]⨾[ r ]⨾⨾ rs) brk sep alloced =
      let sepₗ , sepᵥᵣ , sepₗ,ᵥᵣ = Lemmas.AllPairs.++⁻ (subst Unique (liveAddrs& l (v ⨾⨾ r)) sep) in
      let sepᵥ,ᵣ , sepᵣ = AllPairs.uncons sepᵥᵣ in
      let sepᵥ,ₗ , sepₗ,ᵣ = All.unzipWith All.uncons sepₗ,ᵥᵣ in
      let sepₗᵣ = subst Unique (sym (liveAddrs& l r)) (AllPairs.++⁺ sepₗ sepᵣ sepₗ,ᵣ) in
      let sepᵥ,ₗᵣ = subst (All _) (sym (liveAddrs& l r)) (All.++⁺ (All.map (_∘ sym) sepᵥ,ₗ) sepᵥ,ᵣ) in
      let allocedₗ , allocedᵥᵣ = All.++⁻ _ (subst (All (_< brk)) (liveAddrs& l (v ⨾⨾ r)) alloced) in
      let allocedᵥ , allocedᵣ = All.uncons allocedᵥᵣ in
      let allocedₗᵣ = subst (All (_< brk)) (sym (liveAddrs& l r)) (All.++⁺ allocedₗ allocedᵣ) in
      let tt , sep′ , alloced′ = restructure rs brk sepₗᵣ allocedₗᵣ in
      λ where
        .proj₁        → tt
        .proj₂ .proj₁ →
          All.map [ All.lookup sepᵥ,ₗᵣ , flip <-irrefl ∘ <-≤-trans allocedᵥ ] alloced′ ∷ sep′
        .proj₂ .proj₂ →
          _∷_
          (inj₁ (subst (_ ∈_) (sym (liveAddrs& l (v ⨾⨾ r))) (∈-++⁺ʳ _ (here refl))))
          (All.map
            (⊎.map₁
              ( subst (_ ∈_) (sym (liveAddrs& l (v ⨾⨾ r))) ∘
                Lemmas.∈.++⁺ ∘
                ⊎.map₂ there ∘
                ∈.∈-++⁻ _ ∘
                subst (_ ∈_) (liveAddrs& l r)))
            alloced′)

    separate :
      {s : StateThread} {@0 cond : Condition s} →
      Program s (Erased (Unique (liveRefs cond))) cond (λ _ → cond)
    separate brk sep alloced = erased (Lemmas.AllPairs.map⁻ (λ { p refl → p refl }) sep) , sep , All.tabulate inj₁


@0 Pure : Imperative.Impl
Pure = record { PureImpl }

module @0 Pure = Imperative.Impl Pure
