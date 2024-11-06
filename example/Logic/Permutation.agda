{-# OPTIONS --safe #-}
module Logic.Permutation {ℓ} {A : Set ℓ} where

open import Data.List as List
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Vec as Vec
open import Relation.Binary.PropositionalEquality hiding ([_])

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
