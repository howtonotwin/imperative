module Imperative.ST where

open import Agda.Primitive
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.Nat
open import Data.Unit

open import ArrayValue
import Erased as SafeErased
import Realizer as SafeRealizer

import Imperative
open import Imperative.Slice hiding (Slice; Ref)
open import Imperative.Condition hiding (Condition)
import Imperative.Specifications
open import Imperative.Restructuring

{-# FOREIGN GHC import qualified Control.Monad.ST #-}
{-# FOREIGN GHC import qualified GHC.Arr #-}

private
  module Unsafe where
    postulate
      ST : ∀ {ℓ} → Set ℓ → Set ℓ
      runST : ∀ {ℓ} {A : Set ℓ} → ST A → A
      returnST : ∀ {ℓ} {A : Set ℓ} → A → ST A
      thenST : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} → ST A → (A → ST B) → ST B
    {-# FOREIGN GHC type ST ℓ a = Control.Monad.ST.ST AgdaAny a #-}
    {-# COMPILE GHC ST = type ST #-}
    {-# COMPILE GHC runST = \_ _ x -> Control.Monad.ST.runST (coe x) #-}
    {-# COMPILE GHC returnST = \_ _ -> return #-}
    {-# COMPILE GHC thenST = \_ _ _ _ -> (>>=) #-}

    data Realizer {ℓ} {A : Set ℓ} : @0 A → Set ℓ where
      realized? : (x : A) → Realizer x
    {-# FOREIGN GHC newtype Realizer ℓ a x = Realized a #-}
    {-# COMPILE GHC Realizer = data Realizer (Realized) #-}
    postulate imagined : ∀ {ℓ} {A : Set ℓ} {@0 x : A} → A → Realizer x
    {-# COMPILE GHC imagined = \_ _ _ -> Realized #-}
    realize : ∀ {ℓ} {A : Set ℓ} {@0 x : A} → Realizer x → SafeRealizer.Realizer x
    realize (realized? x) = SafeRealizer.realized x

    record Erased {ℓ} (@0 A : Set ℓ) : Set ℓ where
      constructor erased
      field @0 erasedly : A
    {-# FOREIGN GHC data Erased ℓ a = Erased #-}
    {-# COMPILE GHC Erased = data Erased (Erased) #-}
    postulate blank : ∀ {ℓ} (@0 A : Set ℓ) → Erased A
    {-# COMPILE GHC blank = \_ _ -> Erased #-}
    erase : ∀ {ℓ} {@0 A : Set ℓ} → Erased A → SafeErased.Erased A
    erase (erased x) = SafeErased.erased x

    postulate
      STArray : Set lzero
      readSTArray : ∀ {ℓ} {A : Set ℓ} → STArray → ℕ → ST A
      writeSTArray : ∀ {ℓ} {A : Set ℓ} → STArray → ℕ → A → ST ⊤
      newSTArray : (n : ℕ) → ST STArray
    {-# FOREIGN GHC type STArray = GHC.Arr.STArray AgdaAny Integer AgdaAny #-}
    {-# COMPILE GHC STArray = type STArray #-}
    {-# COMPILE GHC readSTArray =
      \_ _ -> coe (GHC.Arr.readSTArray :: GHC.Arr.STArray s Integer e -> Integer -> Control.Monad.ST.ST s e) #-}
    {-# COMPILE GHC writeSTArray =
      \_ _ -> coe (GHC.Arr.writeSTArray :: GHC.Arr.STArray s Integer e -> Integer -> e -> Control.Monad.ST.ST s ()) #-}
    {-# COMPILE GHC newSTArray = \n -> coe (GHC.Arr.newSTArray (0, n - 1) ()) #-}

  open SafeErased
  open SafeRealizer

  module STImpl where
    abstract
      record StateThread : Setω₀ where constructor mkStateThread
      Array : StateThread → @0 ℕ → Set lzero
      Array _ _ = Unsafe.STArray
      open Imperative.Specifications StateThread Array

      Program : ∀ {ℓ} (s : StateThread) (A : Set ℓ) (@0 pre : Condition s) (@0 post : A → Condition s) → Set ℓ
      Program _ A _ _ = Unsafe.ST A

      runProgram :
        ∀ {ℓ} {A : Set ℓ} →
        ({s : StateThread} → Program s A 𝟏 (λ _ → 𝟏)) → A
      runProgram x = Unsafe.runST (x {mkStateThread})

      return :
        ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 cond : A → Condition s}
        (x : A) → Program s A (cond x) cond
      return x = Unsafe.returnST x

      _>>=_ :
        ∀ {s : StateThread} {ℓA ℓB} {A : Set ℓA} {B : Set ℓB}
        {@0 pre : Condition s} {@0 mid : A → Condition s} {@0 post : B → Condition s} →
        Program s A pre mid → ((x : A) → Program s B (mid x) post) → Program s B pre post
      _>>=_ = Unsafe.thenST

      read :
        ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 x : A}
        (r : Ref s) → Program s (Realizer x) (r ↦ x ⨾ 𝟏) (λ _ → r ↦ x ⨾ 𝟏)
      read (slice a i _) = Unsafe.thenST (Unsafe.readSTArray a i) λ x → Unsafe.returnST (Unsafe.realize x)

      write :
        ∀ {s : StateThread} {@0 ℓA} {ℓB} {@0 A : Set ℓA} {B : Set ℓB} {@0 x : A}
        (r : Ref s) (y : B) → Program s ⊤ (r ↦ x ⨾ 𝟏) (λ _ → r ↦ y ⨾ 𝟏)
      write (slice a i _) y = Unsafe.writeSTArray a i y

      allocArray :
        {s : StateThread} (n : ℕ) → Program s (Array s n) 𝟏 (λ a → fullSlice a ↦＊ ArrayValue.replicate n tt)
      allocArray n = Unsafe.newSTArray n

      frame :
        ∀ {s : StateThread} {ℓ} {A : Set ℓ}
        (@0 side : Condition s) {@0 pre : Condition s} {@0 post : A → Condition s} →
        Program s A pre post → Program s A (pre & side) (λ x → post x & side)
      frame _ x = x

      restructure :
        {s : StateThread} {@0 pre post : Condition s} →
        @0 Restructuring pre post → Program s ⊤ pre (λ _ → post)
      restructure _ = Unsafe.returnST tt

      separate :
        {s : StateThread} {@0 cond : Condition s} →
        Program s (Erased (Unique (liveRefs cond))) cond (λ _ → cond)
      separate = Unsafe.returnST (Unsafe.erase (Unsafe.blank _))

ST : Imperative.Impl
ST = record { STImpl }

module ST = Imperative.Impl ST
