module Imperative.ST where

open import Agda.Primitive
open import Data.Unit
open import Level

import Imperative
import Realizer as SafeRealizer

{-# FOREIGN GHC import qualified Control.Monad.ST #-}
{-# FOREIGN GHC import qualified Data.STRef #-}

private
  module Unsafe where
    record StateThread : SSetω₀ where constructor mkStateThread

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
    postulate
      imagined : ∀ {ℓ} {A : Set ℓ} {@0 x : A} → A → Realizer x
    {-# COMPILE GHC imagined = \_ _ _ -> Realized #-}
    realize : ∀ {ℓ} {A : Set ℓ} {@0 x : A} → Realizer x → SafeRealizer.Realizer x
    realize (realized? x) = SafeRealizer.realized x

    postulate
      STRef : Set lzero
      readSTRef : ∀ {ℓ} {A : Set ℓ} → STRef → ST A
      writeSTRef : ∀ {ℓ} {A : Set ℓ} → STRef → A → ST ⊤
      newSTRef : ST STRef
    {-# FOREIGN GHC type STRef = Data.STRef.STRef AgdaAny AgdaAny #-}
    {-# COMPILE GHC STRef = type STRef #-}
    {-# COMPILE GHC readSTRef = \_ _ -> coe Data.STRef.readSTRef #-}
    {-# COMPILE GHC writeSTRef = \_ _ -> coe Data.STRef.writeSTRef #-}
    {-# COMPILE GHC newSTRef = Data.STRef.newSTRef (coe ()) #-}

  open SafeRealizer

  module STImpl where
    abstract
      StateThread : SSetω₀
      StateThread = Unsafe.StateThread
      Ref : StateThread → Set lzero
      Ref _ = Unsafe.STRef

      open Imperative.Spec StateThread Ref public

      Program :
        ∀ {ℓA ℓpre ℓpost} (s : StateThread) (A : Set ℓA)
        (@0 pre : Condition s ℓpre) (@0 post : A → Condition s ℓpost) → Set (ℓA ⊔ ℓpre ⊔ ℓpost)
      Program {ℓA} {ℓpre} {ℓpost} _ A _ _ = Lift (ℓA ⊔ ℓpre ⊔ ℓpost) (Unsafe.ST A)

      runProgram :
        ∀ {ℓA ℓpost} {A : Set ℓA} {@0 post : (s : StateThread) → A → Condition s ℓpost} →
        ({s : StateThread} → Program s A 𝟏 (post s)) → A
      runProgram x = Unsafe.runST (x {Unsafe.mkStateThread} .lower)

      return :
        ∀ {s : StateThread} {ℓA ℓcond} {A : Set ℓA} {@0 cond : A → Condition s ℓcond}
        (x : A) → Program s A (cond x) cond
      return x .lower = Unsafe.returnST x

      _>>=_ :
        ∀ {s : StateThread} {ℓA ℓB ℓpre ℓmid ℓpost} {A : Set ℓA} {B : Set ℓB}
        {@0 pre : Condition s ℓpre} {@0 mid : A → Condition s ℓmid} {@0 post : B → Condition s ℓpost} →
        Program s A pre mid → ((x : A) → Program s B (mid x) post) → Program s B pre post
      (x >>= f) .lower = Unsafe.thenST (x .lower) λ x → f x .lower

      read :
        ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 x : A}
        (r : Ref s) → Program s (Realizer x) (r ↦ x ⨾ 𝟏) (λ _ → r ↦ x ⨾ 𝟏)
      read r .lower = Unsafe.thenST (Unsafe.readSTRef r) λ x → Unsafe.returnST (Unsafe.realize x)

      write :
        ∀ {s : StateThread} {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {@0 x : A}
        (r : Ref s) (y : B) → Program s ⊤ (r ↦ x ⨾ 𝟏) (λ _ → r ↦ y ⨾ 𝟏)
      write r y .lower = Unsafe.writeSTRef r y

      alloc : {s : StateThread} → Program s (Ref s) 𝟏 (λ r → r ↦ tt ⨾ 𝟏)
      alloc .lower = Unsafe.newSTRef

      frame :
        ∀ {s : StateThread} {ℓA ℓpre ℓpost ℓside} {A : Set ℓA}
        (@0 side : Condition s ℓside) {@0 pre : Condition s ℓpre} {@0 post : A → Condition s ℓpost} →
        Program s A pre post → Program s A (side & pre) (λ x → side & post x)
      frame _ x .lower = x .lower

      restructure :
        ∀ {s : StateThread} {ℓpre ℓpost} {@0 pre : Condition s ℓpre} {@0 post : Condition s ℓpost} →
        @0 Restructuring pre post → Program s ⊤ pre (λ _ → post)
      restructure _ .lower = Unsafe.returnST tt

ST : Imperative.Impl
ST = record { STImpl }

module ST = Imperative.Impl ST
