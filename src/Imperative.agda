{-# OPTIONS --safe #-}
-- interface of types and operations needed to embed and run correct by
-- construction imperative programs in Agda, packaged as a record
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

open import Imperative.Slice hiding (Slice; Ref)
open import Imperative.Condition hiding (Condition)
import Imperative.Specifications
open import Imperative.Restructuring
open import Imperative.Framing

record Impl : Setω₁ where
  field
    -- tokens that identify what state the other operations should access
    -- must live in a larger universe than runProgram can return
    -- (also reflects the phantom type parameter that ST uses to ensure purity)
    StateThread : Setω₀
    -- memory allocations, indexed by size
    -- note that an Array specifies a region of memory, but accesses are made
    -- through slices
    Array : StateThread → @0 ℕ → Set lzero
  -- pull in auxiliary data types, specialized to above fields
  open Imperative.Specifications StateThread Array public

  field
    -- a `Program s A pre post` is a sequence of instructions that can run in
    -- the state thread s atop a heap initially described by pre (the
    -- *precondition*) and will terminate by returning a value x : A while
    -- leaving the heap in state (post x) (the *postcondition*)
    Program : ∀ {ℓ} (s : StateThread) (A : Set ℓ) (@0 pre : Condition s) (@0 post : A → Condition s) → Set ℓ

    -- the result of an imperative program that does not access any external
    -- state, as a pure function of the program
    -- the requirements that the pre- and post-conditions be empty is probably
    -- not strictly necessary as there should not be a way to write appropriate
    -- nontrivial terms for them anyway, but it makes inference better
    runProgram :
      ∀ {ℓ} {A : Set ℓ} →
      ({s : StateThread} → Program s A 𝟏 (λ _ → 𝟏)) → A

    -- return a value without doing anything, potentially generalizing the heap
    -- description
    return :
      ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 cond : A → Condition s}
      (x : A) → Program s A (cond x) cond

    -- monad-like operator that produces a program by putting two subprograms in
    -- sequence, enforcing that the postcondition of the first matches the
    -- precondition of the second
    _>>=_ :
      ∀ {s : StateThread} {ℓA ℓB} {A : Set ℓA} {B : Set ℓB}
      {@0 pre : Condition s} {@0 mid : A → Condition s} {@0 post : B → Condition s} →
      Program s A pre mid → ((x : A) → Program s B (mid x) post) → Program s B pre post

    -- program that reads a certain reference (producing a non-erased
    -- realization of the potentially-erased value known to be behind the
    -- reference)
    -- note: by fiat, the type of a value must be known, non-erased, to read it
    read :
      ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 x : A}
      (r : Ref s) → Program s (Realizer x) (r ↦ x ⨾ 𝟏) (λ _ → r ↦ x ⨾ 𝟏)

    -- program that overwrites the contents of a memory cell with a new value
    -- note: by fiat, the type of a value does not need to be known, non-erased
    -- to overwrite it, but the type of the value being written does need to be
    -- known, non-erased
    write :
      ∀ {s : StateThread} {@0 ℓA} {ℓB} {@0 A : Set ℓA} {B : Set ℓB} {@0 x : A}
      (r : Ref s) (y : B) → Program s ⊤ (r ↦ x ⨾ 𝟏) (λ _ → r ↦ y ⨾ 𝟏)

    -- program that makes a new memory allocation of a certain size, filled with
    -- the dummy value `tt`
    allocArray :
      {s : StateThread} (n : ℕ) →
      Program s (Array s n) 𝟏 (λ r → fullSlice r ↦* ArrayValue.replicate n tt)

    -- extension of a program to run on a bigger heap than specified in its
    -- precondition by separately conjoining a side-condition to the
    -- precondition that is also preserved to the postcondition
    frame :
      ∀ {s : StateThread} {ℓ} {A : Set ℓ}
      (@0 side : Condition s) {@0 pre : Condition s} {@0 post : A → Condition s} →
      Program s A pre post → Program s A (pre & side) (λ x → post x & side)

    -- application of "changes" to the heap that do not actually require any
    -- action (that is, only the specification describing what is in the heap
    -- changes)
    restructure :
      {s : StateThread} {@0 pre post : Condition s} →
      @0 Restructuring pre post → Program s ⊤ pre (λ _ → post)

    -- reflection of the separation logic principle that all the live references
    -- in any reachable heap description are distinct as a proof usuable in the
    -- program
    -- (not particularly common to use but here for completeness)
    separate : {s : StateThread} {@0 cond : Condition s} → Program s (Erased (Unique (liveRefs cond))) cond (λ _ → cond)
  -- now some basic utilities (not fields!) defined in terms of the primitives

  -- Agda uses _>>_ instead of _>>=_ when desugaring `do { stmt; stmts... }`
  -- so this is needed in order to get reasonable do-notation for Program
  -- the heap state after a discarded-value statement might still depend on the
  -- value returned, so `_>>_` is actually identical to `_>>=_` but gives the
  -- "discarded" value to the continuation as an *implicit* argument
  -- might be possible to require that the heap state after a discarded-value
  -- statement not depend on the returned value
  _>>_ :
      ∀ {s : StateThread} {ℓA ℓB} {A : Set ℓA} {B : Set ℓB}
      {@0 pre : Condition s} {@0 mid : A → Condition s} {@0 post : B → Condition s} →
      Program s A pre mid → ({x : A} → Program s B (mid x) post) → Program s B pre post
  p >> q = do
    x ← p
    q {x}

  -- writes a realized value while putting another (equal) value into the heap
  -- description
  writeRealized :
    ∀ {s : StateThread} {@0 ℓA} {ℓB} {@0 A : Set ℓA} {B : Set ℓB} {@0 x : A} {@0 y : B}
    (r : Ref s) → Realizer y → Program s ⊤ (r ↦ x ⨾ 𝟏) (λ _ → r ↦ y ⨾ 𝟏)
  writeRealized r (realized y) = write r y

  -- utility that allocates a single memory cell
  alloc : {s : StateThread} → Program s (Ref s) 𝟏 (λ r → r ↦ tt ⨾ 𝟏)
  alloc = do
    a ← allocArray 1 -- allocArray 1 : Program s (Array s 1) 𝟏 (λ r → fullSlice r ↦ tt ⨾ 𝟏)
    return (fullSlice a)

  -- utility that both allocates a memory cell and sets it to a given value
  init : ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 x : A} → Realizer x → Program s (Ref s) 𝟏 (λ r → r ↦ x ⨾ 𝟏)
  init x = do
    v ← alloc
    writeRealized v x
    return v

  -- combination of restructure and frame, making a for invoking subprograms
  -- (capable of simultaneously selecting certain parts of the heap to focus
  -- with frame and reorganizing the selection)
  reframe :
    ∀ {s : StateThread} {ℓ} {A : Set ℓ} {@0 pre focus side : Condition s} {@0 post : A → Condition s} →
    @0 Framing pre focus side → Program s A focus post → Program s A pre (λ x → post x & side)
  reframe f p = do
    restructure (cancelFraming f)
    frame _ p

  -- unfortunately cannot import automation (Imperative.AutomaticStyle) here

  -- overwrites a whole Slice by an ArrayValue by using write repeatedly
  writeSlice :
    {s : StateThread} {@0 n : ℕ} {@0 pre : ArrayValue n} (arr : Slice s n) (xs : ArrayValue n) →
    Program s ⊤ (arr ↦* pre) (λ _ → arr ↦* xs)
  writeSlice {pre = []}      arr []       = return tt
  writeSlice {pre = p ∷ pre} arr (x ∷ xs) = do
    frame (++ arr ↦* _) (write (* arr) x)
    restructure (unfocus (((* arr ⨾⨾ 𝟏) &> >[ ++ arr ↦* _ ]<) <&> >[ * arr ⨾⨾ 𝟏 ]<))
    frame (* arr ⨾⨾ 𝟏) (writeSlice (++ arr) xs)
    restructure (unfocus (((++ arr ↦* _) &> >[ * arr ⨾⨾ 𝟏 ]<) <&> (>[ ++ arr ↦* _ ]< <& 𝟏)))

  -- reads a whole Slice to a Vec (of homogenous type)
  -- would need a witness for the list of types to make heterogenous
  readVec :
    ∀ {s : StateThread} {ℓ} {A : Set ℓ} {n : ℕ} (arr : Slice s n) {@0 xs : Vec A n} →
    Program s (Realizer xs) (arr ↦* vec xs) (λ _ → arr ↦* vec xs)
  readVec {n = zero}  arr {xs = []}     = return (realized [])
  readVec {n = suc n} arr {xs = x ∷ xs} = do
    realized .x ← frame (++ arr ↦* _) (read (* arr))
    realized .xs ← reframe ((* arr ⨾⨾ 𝟏) &> >[ ++ arr ↦* _ ]<) (readVec (++ arr))
    restructure (unfocus (((++ arr ↦* _) &> >[ * arr ⨾⨾ 𝟏 ]<) <&> (>[ ++ arr ↦* _ ]< <& 𝟏)))
    return (realized (x ∷ xs))

-- implementations in Imperative.Pure and Imperative.ST
-- conveniences for importing in Imperative.ManualStyle and
-- Imperative.AutomaticStyle
