{-# OPTIONS --safe #-}
open import Agda.Primitive
open import Data.Nat
module Imperative.Specifications (StateThread : Setω₀) (Array : StateThread → @0 ℕ → Set lzero) where

open import Data.List
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.Nat.Properties
open import Data.Unit
open import Relation.Binary.PropositionalEquality renaming (trans to infixl 1 _∙_)

open import ArrayValue
open import Erased
open import Realizer

record Slice (s : StateThread) (@0 n : ℕ) : Set lzero where
  constructor slice
  field
    @0 {underlyingLength} : ℕ
    underlying : Array s underlyingLength
    offset : ℕ
    @0 .fit : offset + n ≤ underlyingLength
Ref : StateThread → Set lzero
Ref s = Slice s 1
fullSlice : {s : StateThread} {@0 n : ℕ} → Array s n → Slice s n
fullSlice a = slice a 0 ≤-refl
infixl 10 _[_because_] _[_∶+_because_]
_[_∶+_because_] : {s : StateThread} {@0 n : ℕ} → Slice s n → (i l : ℕ) → @0 .(l + i ≤ n) → Slice s l
slice a o fit [ i ∶+ l because p ] =
  let @0 n : _; n = _ in
  slice a (i + o)
    (≤-trans
      (subst (_≤ o + n)
        (cong (o +_) (+-comm l i) ∙ sym (+-assoc o i l) ∙ cong (_+ l) (+-comm o i))
        (+-monoʳ-≤ o p))
      fit)
_[_because_] : {s : StateThread} {@0 n : ℕ} → Slice s n → (i : ℕ) → @0 .(i < n) → Ref s
_[_because_] = _[_∶+ 1 because_]
substSlice : {s : StateThread} {@0 n m : ℕ} → @0 .(n ≡ m) → Slice s n → Slice s m
substSlice e (slice a o p) = slice a o (subst _ e p)

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

infix 1 _↦＊_
_↦＊_ : {s : StateThread} {@0 n : ℕ} → Slice s n → ArrayValue n → Condition s
s ↦＊ []     = 𝟏
s ↦＊ x ∷ xs =
  let @0 n : _; n = _ in
  s [ 0 because z<s ] ↦ x ⨾ s [ 1 ∶+ _ because subst (_≤ suc n) (+-comm 1 _) ≤-refl ] ↦＊ xs

infixr -1 [_]&[_]⨾[_]⨾⨾_
data Restructuring {s : StateThread} : Condition s → Condition s → Setω₀ where
  [_]╳ : (discards : Condition s) → Restructuring discards 𝟏
  [_]&[_]⨾[_]⨾⨾_ :
    ∀ (l : Condition s)
    (v : Ref s) {ℓ} {A : Set ℓ} {x : A}
    (r : Condition s) {rest : Condition s} →
    Restructuring (l & r) rest →
    Restructuring (l & v ↦ x ⨾ r) (v ↦ x ⨾ rest)
pattern ╳ = [ _ ]╳
pattern ∎ = [ 𝟏 ]╳
