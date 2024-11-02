{-# OPTIONS --safe #-}
module InsertionSort where

open import Agda.Primitive
open import Function
open import Data.Maybe hiding (_>>=_)
open import Data.Maybe.Relation.Binary.Connected hiding (refl; sym)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.List as List
open import Data.List.Properties as List
open import Data.List.Relation.Unary.Linked
open import Data.List.Relation.Unary.Sorted.TotalOrder ≤-totalOrder
import Data.List.Relation.Unary.Sorted.TotalOrder.Properties as Sorted
open import Data.Product
open import Data.Sum as ⊎
open import Data.Unit
import Data.Vec as Vec
open Vec using (Vec; []; _∷_)
import Data.Vec.Properties as Vec
open import Relation.Binary.PropositionalEquality renaming (trans to infixl 1 _∙_) hiding ([_])
open import Relation.Nullary.Decidable

open import ArrayValue
open import Erased
open import LargeEq
open import Realizer

import Imperative
import Imperative.ManualStyle

private
  Sorted-++⁻ : ∀ {xs ys} → Sorted (xs List.++ ys) → Sorted xs × Connected _≤_ (List.last xs) (List.head ys) × Sorted ys
  Sorted-++⁻ {[]}           {[]}     []        = [] , nothing , []
  Sorted-++⁻ {[]}           {y ∷ ys} p         = [] , nothing-just , p
  Sorted-++⁻ {x₁ ∷ []}      {[]}     [-]       = [-] , just-nothing , []
  Sorted-++⁻ {x₁ ∷ []}      {y ∷ ys} (p₁ ∷ p₂) = [-] , just p₁ , p₂
  Sorted-++⁻ {x₁ ∷ x₂ ∷ xs} {ys}     (p₁ ∷ p₂) =
    let q₁ , q₂ , q₃ = Sorted-++⁻ p₂ in
    p₁ ∷ q₁ , q₂ , q₃

  Vec-toList-∷ʳ : ∀ {ℓ} {A : Set ℓ} {n : ℕ} (xs : Vec A n) (y : A) → Vec.toList (xs Vec.∷ʳ y) ≡ Vec.toList xs List.∷ʳ y
  Vec-toList-∷ʳ []       y = refl
  Vec-toList-∷ʳ (x ∷ xs) y = cong (x ∷_) (Vec-toList-∷ʳ xs y)

  List-last-∷ʳ : ∀ {ℓ} {A : Set ℓ} (xs : List A) (y : A) → List.last (xs List.∷ʳ y) ≡ just y
  List-last-∷ʳ []           y = refl
  List-last-∷ʳ (_ ∷ [])     y = refl
  List-last-∷ʳ (_ ∷ x ∷ xs) y = List-last-∷ʳ (x ∷ xs) y

module _ {ℓ} {A : Set ℓ} where
  data Insertion (x : A) : {n : ℕ} → Vec A n → Vec A (suc n) → Set ℓ where
    here  : {n : ℕ} {xs : Vec A n} → Insertion x xs (x ∷ xs)
    there : {n : ℕ} {xs : Vec A n} {ys : Vec A (suc n)} {y : A} → Insertion x xs ys → Insertion x (y ∷ xs) (y ∷ ys)
  ereh : {x : A} {n : ℕ} {xs : Vec A n} → Insertion x xs (xs Vec.∷ʳ x)
  ereh {xs = []}     = here
  ereh {xs = y ∷ xs} = there ereh
  ereht :
    {x : A} {n : ℕ} {xs : Vec A n} {ys : Vec A (suc n)} {y : A} →
    Insertion x xs ys → Insertion x (xs Vec.∷ʳ y) (ys Vec.∷ʳ y)
  ereht here      = here
  ereht (there i) = there (ereht i)
  commuteInsertions :
    {n : ℕ} {x₁ x₂ : A} {xs₁ : Vec A n} {xs₂ : Vec A (suc n)} {xs₃ : Vec A (suc (suc n))} →
    Insertion x₁ xs₁ xs₂ → Insertion x₂ xs₂ xs₃ →
    Σ[ xs₂′ ∈ Vec A (suc n) ] Insertion x₂ xs₁ xs₂′ × Insertion x₁ xs₂′ xs₃
  commuteInsertions i         here      = _ , here , there i
  commuteInsertions here      (there j) = _ , j    , here
  commuteInsertions (there i) (there j) =
    let _ , j′ , i′ = commuteInsertions i j in
    _ , there j′ , there i′

  infixr 5 _∷_
  data Permutation : {n : ℕ} → Vec A n → Vec A n → Set ℓ where
    []  : Permutation [] []
    _∷_ :
      {n : ℕ} {x : A} {xs ys′ : Vec A n} {ys : Vec A (suc n)} →
      Insertion x ys′ ys → Permutation ys′ xs → Permutation ys (x ∷ xs)
  ixPermutation :
    {n : ℕ} {xs ys : Vec A (suc n)} {x : A} {ys′ : Vec A n} →
    Insertion x ys′ ys → Permutation xs ys →
    Σ[ xs′ ∈ Vec A n ] Insertion x xs′ xs × Permutation xs′ ys′
  ixPermutation here      (j ∷ js) = _ , j , js
  ixPermutation (there i) (j ∷ js) =
    let _ , k , ks = ixPermutation i js in
    let _ , j′ , k′ = commuteInsertions k j in
    _ , k′ , j′ ∷ ks
  locateHead :
    {n : ℕ} {x : A} {xs : Vec A n} {ys : Vec A (suc n)} → Permutation (x ∷ xs) ys →
    Σ[ ys′ ∈ Vec A n ] Insertion x ys′ ys × Permutation xs ys′
  locateHead (here    ∷ is) = _ , here , is
  locateHead (there i ∷ is) =
    let _ , j , is′ = locateHead is in
    _ , there j , i ∷ is′
  Permutation-refl : {n : ℕ} {xs : Vec A n} → Permutation xs xs
  Permutation-refl {xs = []}     = []
  Permutation-refl {xs = x ∷ xs} = here ∷ Permutation-refl
  Permutation-trans : {n : ℕ} {xs ys zs : Vec A n} → Permutation xs ys → Permutation ys zs → Permutation xs zs
  Permutation-trans [] []       = []
  Permutation-trans is (j ∷ js) =
    let _ , i , is′ = ixPermutation j is in
    i ∷ Permutation-trans is′ js
  Permutation-sym : {n : ℕ} {xs ys : Vec A n} → Permutation xs ys → Permutation ys xs
  Permutation-sym {xs = []}     [] = []
  Permutation-sym {xs = x ∷ xs} is =
    let _ , i , is′ = locateHead is in
    i ∷ Permutation-sym is′

  Insertion-unique :
    {n : ℕ} {x : A} {xs : Vec A n} {ys zs : Vec A (suc n)} →
    Insertion x xs ys → Insertion x xs zs → Permutation ys zs
  Insertion-unique here      here      = Permutation-refl
  Insertion-unique (there i) here      = there i ∷ Permutation-refl
  Insertion-unique here      (there j) = there here ∷ Insertion-unique here j
  Insertion-unique (there i) (there j) = here ∷ Insertion-unique i j

  cast-Insertion :
    {n m : ℕ} {x : A} {xs : Vec A n} {ys : Vec A (suc n)} (e : n ≡ m) →
    Insertion x xs ys → Insertion x (Vec.cast e xs) (Vec.cast (cong suc e) ys)
  cast-Insertion             e here      = here
  cast-Insertion {m = suc m} e (there i) = there (cast-Insertion (cong pred e) i)
  cast-Permutation :
    {n m : ℕ} {xs ys : Vec A n} (e : n ≡ m) →
    Permutation xs ys → Permutation (Vec.cast e xs) (Vec.cast e ys)
  cast-Permutation {m = zero}  e []       = []
  cast-Permutation {m = suc m} e (i ∷ is) = cast-Insertion e′ i ∷ cast-Permutation e′ is
    where e′ = cong pred e

  ++-Insertionˡ :
    {n m : ℕ} (zs : Vec A m) {x : A} {xs : Vec A n} {ys : Vec A (suc n)} →
    Insertion x xs ys → Insertion x (xs Vec.++ zs) (ys Vec.++ zs)
  ++-Insertionˡ zs here      = here
  ++-Insertionˡ zs (there i) = there (++-Insertionˡ zs i)
  ++-Permutationˡ :
    {n m : ℕ} (zs : Vec A m) {xs ys : Vec A n} →
    Permutation xs ys → Permutation (xs Vec.++ zs) (ys Vec.++ zs)
  ++-Permutationˡ zs []       = Permutation-refl
  ++-Permutationˡ zs (i ∷ is) = ++-Insertionˡ zs i ∷ ++-Permutationˡ zs is

  last-Insertion :
    {n : ℕ} {x : A} {xs : Vec A n} {ys : Vec A (suc n)} → Insertion x xs ys →
    List.last (Vec.toList ys) ≡ just x ⊎ List.last (Vec.toList ys) ≡ List.last (Vec.toList xs)
  last-Insertion {xs = []}         {x ∷ []}     here      = inj₁ refl
  last-Insertion {xs = y ∷ xs}     {x ∷ y ∷ xs} here      = inj₂ refl
  last-Insertion {xs = y ∷ xs}     {y ∷ z ∷ ys} (there i) with last-Insertion i
  last-Insertion {xs = y ∷ xs}     {y ∷ z ∷ ys} (there i) | inj₁ e  = inj₁ e
  last-Insertion {xs = y ∷ []}     {y ∷ z ∷ []} (there i) | inj₂ ()
  last-Insertion {xs = y ∷ z ∷ xs} {y ∷ ys}     (there i) | inj₂ e  = inj₂ e

module _ (I : Imperative.Impl) where
  open Imperative.ManualStyle I

  private
    module _ {s : StateThread} where
      private
        record Bundle (n : ℕ) (@0 m : ℕ) (combined : Slice s (n + m)) : Setω₀ where
          field
            left : Slice s n
            right : Slice s m
            @0 eqn :
              (xs : ArrayValue n) (ys : ArrayValue m) →
              combined ↦＊ xs ArrayValue.++ ys ≡ω₀ left ↦＊ xs & right ↦＊ ys
        open Bundle
        mkBundle : (n : ℕ) (@0 m : ℕ) (combined : Slice s (n + m)) → Bundle n m combined
        mkBundle n       m combined .left  = combined [ 0 ∶+ n because +-monoʳ-≤ n z≤n ]
        mkBundle n       m combined .right = combined [ n ∶+ m because subst (_≤ n + m) (+-comm n m) ≤-refl ]
        mkBundle zero    m combined .eqn   []       ys = reflω₀
        mkBundle (suc n) m combined .eqn   (x ∷ xs) ys =
          let left′ = _ in
          congω₀ (* combined ↦ x ⨾_)
            (    mkBundle n m (++ combined) .eqn xs ys
             ∙ω₀ congω₀↑ (λ s → left′ ↦＊ xs & s ↦＊ ys) (eqSlice refl refl (+-suc n _)))
      module Split++ (n : ℕ) (@0 m : ℕ) (combined : Slice s (n + m)) = Bundle (mkBundle n m combined)

      infixl 10 _[-1] _[∶-1]
      _[-1] : {n : ℕ} → Slice s (suc n) → Ref s
      _[-1] {n} = _[ n because n<1+n n ]
      _[∶-1] : {@0 n : ℕ} → Slice s (suc n) → Slice s n
      _[∶-1] {n} = _[ 0 ∶+ n because subst (_≤ suc n) (+-comm 0 n) (n≤1+n n) ]

      split∷ʳ :
        ∀ {n : ℕ} {ℓ} {A : Set ℓ} (snoc : Slice s (suc n)) (xs : ArrayValue n) (y : A) →
        snoc ↦＊ (xs ArrayValue.∷ʳ y) ≡ω₀ snoc [∶-1] ↦＊ xs & snoc [-1] ↦ y ⨾ 𝟏
      split∷ʳ snoc []       y = reflω₀
      split∷ʳ snoc (x ∷ xs) y =
        congω₀ (* snoc ↦ x ⨾_)
          (split∷ʳ (++ snoc) xs y ∙ω₀ congω₀↑ (λ r → ++ snoc [∶-1] ↦＊ xs & r ↦ y ⨾ 𝟏) (eqSlice refl refl (+-suc _ _)))

      substSlice-cast :
        {n m : ℕ} (e : n ≡ m) (arr : Slice s n) (xs : ArrayValue m) →
        substSlice e arr ↦＊ xs ≡ω₀ arr ↦＊ ArrayValue.cast (sym e) xs
      substSlice-cast {zero}  e arr []       = reflω₀
      substSlice-cast {suc n} e arr (x ∷ xs) = congω₀ (* arr ↦ x ⨾_) (substSlice-cast (cong pred e) (++ arr) xs)

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
    restructure [! congω₀ (arr ↦＊_) (vec∷ʳ _ _) ∙ω₀ split∷ʳ arr _ _ !]∎
    realized .y ← frame (>[ arr [∶-1] ↦＊ _ ]< <& (arr [-1] ⨾⨾ 𝟏)) do
      restructure [! congω₀ (arr [∶-1] ↦＊_) (vec∷ʳ _ _) ∙ω₀ split∷ʳ (arr [∶-1]) _ _ !]∎
      y′ ← frame ((arr [∶-1] [∶-1] ↦＊ _) &> >[ arr [∶-1] [-1] ⨾⨾ 𝟏 ]<) (read (arr [∶-1] [-1]))
      restructure (unfocus (
            ((arr [∶-1] [-1] ⨾⨾ 𝟏) &> (>[ arr [∶-1] [∶-1] ↦＊ _ ]< <& 𝟏))
        <&> >[ arr [∶-1] [-1] ⨾⨾ 𝟏 ]<))
      restructure [! symω₀ (congω₀ (arr [∶-1] ↦＊_) (vec∷ʳ _ _) ∙ω₀ split∷ʳ (arr [∶-1]) _ _) !]∎
      return y′
    case y ≤? x of λ where
      (yes y≤x) → do
        frame ((arr [∶-1] ↦＊ _) &> >[ arr [-1] ⨾⨾ 𝟏 ]<) (write (arr [-1]) x)
        restructure (unfocus (((arr [-1] ⨾⨾ 𝟏) &> (>[ arr [∶-1] ↦＊ _ ]< <& 𝟏)) <&> >[ arr [-1] ⨾⨾ 𝟏 ]<))
        restructure [! symω₀ (congω₀ (arr ↦＊_) (vec∷ʳ _ _) ∙ω₀ split∷ʳ arr _ _) !]∎
        return (erased (
          pre Vec.∷ʳ y Vec.∷ʳ x ,
          ereh ,
          subst Sorted
            (sym (Vec-toList-∷ʳ (pre Vec.∷ʳ y) x))
            (Sorted.++⁺ ≤-totalOrder
              p
              (subst (λ y → Connected _≤_ y (just x))
                (sym (cong List.last (Vec-toList-∷ʳ pre y) ∙ List-last-∷ʳ (Vec.toList pre) y))
                (just y≤x))
              [-])))
      (no  y≰x) → do
        frame ((arr [∶-1] ↦＊ _) &> >[ arr [-1] ⨾⨾ 𝟏 ]<) (write (arr [-1]) y)
        erased (post , i , sorted) ←
          frame ((arr [-1] ⨾⨾ 𝟏) &> (>[ arr [∶-1] ↦＊ _ ]< <& 𝟏))
            (insert n (arr [∶-1]) pre x (Sorted-++⁻ (subst Sorted (Vec-toList-∷ʳ pre y) p) .proj₁))
        restructure [! symω₀ (congω₀ (arr ↦＊_) (vec∷ʳ _ _) ∙ω₀ split∷ʳ arr _ _) !]∎
        return (erased (
          post Vec.∷ʳ y ,
          ereht i ,
          subst Sorted
            (sym (Vec-toList-∷ʳ post y))
            (Sorted.++⁺ ≤-totalOrder
              sorted
              (case last-Insertion i of λ @0 where
                (inj₁ e) → subst (λ x′ → Connected _≤_ x′ (just y)) (sym e) (just (≰⇒≥ y≰x))
                (inj₂ e) →
                  subst (λ x′ → Connected _≤_ x′ (just y))
                    (sym e)
                    (Sorted-++⁻ (subst Sorted (Vec-toList-∷ʳ pre y) p) .proj₂ .proj₁))
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
    let module Halves = Split++ i (suc m) arr
    let eqn = +-suc i m
    let arr′ = substSlice eqn arr
    let module Halves′ = Split++ (suc i) m arr′
    restructure [! congω₀ (arr ↦＊_) (vec++ sorted (x ∷ xs)) ∙ω₀ Halves.eqn (vec sorted) (vec (x ∷ xs)) !]∎
    realized .x ←
      frame
        ((Halves.left ↦＊ _) &> (>[ * Halves.right ⨾⨾ 𝟏 ]< <& (++ Halves.right ↦＊ _)))
        (read (* Halves.right))
    erased (sorted₁ , x∈sorted₁ , isSorted₁) ← frame
      (    ((* Halves.right ⨾⨾ 𝟏) &> (>[ Halves.left ↦＊ _ ]< <& (++ Halves.right ↦＊ _)))
       <&> (>[ * Halves.right ⨾⨾ 𝟏 ]< <& (++ Halves.right ↦＊ _)))
      do
        restructure [! symω₀ (congω₀ (Halves′.left ↦＊_) (vec∷ʳ _ _) ∙ω₀ split∷ʳ Halves′.left _ _) !]∎
        insert i Halves′.left sorted x isSorted
    restructure [! symω₀ (congω₀ (arr′ ↦＊_) (vec++ _ xs) ∙ω₀ Halves′.eqn (vec _) (vec xs)) !]∎
    erased (sorted₂ , sorting , isSorted₂) ← insertionSort (suc i) m arr′ sorted₁ xs isSorted₁
    restructure [! substSlice-cast eqn arr _ ∙ω₀ congω₀ (arr ↦＊_) (symω₀ (vec-cast (sym eqn) _)) !]∎
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
