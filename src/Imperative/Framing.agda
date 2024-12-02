{-# OPTIONS --safe #-}
-- divisions of a heap, representing the conditions under which a program can
-- invoke a subprogram that only accesses a certain portion of the heap and
-- expect the remainder of the heap to be preserved

-- a simple definition: if a heap description can be written as a separate
-- conjunction (pre & side), then a subprogram with precondition pre and
-- postcondition post can run and results in the postcondition (post & side).
-- this definition is simple and is used to type frame in Imperative.Impl, but
-- using this definition is annoying (lots of restructure-ing is needed).
-- a more complicated definition permits a more sophisticated frame that reduces
-- to the simple one but is more convenient and amenable to automation.
module Imperative.Framing where

open import Agda.Primitive
open import Data.Nat

open import LargeEq

open import Imperative.Condition
open import Imperative.Restructuring

module _ {Ref : Set lzero} where

  -- a Framing i o d exists exactly when o forms a subpart of i (possibly in a
  -- different order) and d is the remainder of i once o is removed (in the same
  -- order as it appears in i)
  -- rely on the (relatively simple) definition of Restructuring and just add an
  -- index
  data Framing (outer inner : Condition Ref) : Condition Ref → Setω₀ where
    focus : (p : Restructuring outer inner) → Framing outer inner (discards p)
  unfocus : {o i d : Condition Ref} → Framing o i d → Restructuring o i
  unfocus (focus p) = p

  -- analogues of Restructuring constructors as Framing introduction rules
  -- the arrows are supposed to point at the part of the Condition that is being
  -- "focused"
  -- these are not very useful on their own as discards already computes on
  -- Restructuring's constructors

  -- focus on "nothing" (𝟏)
  >[_]╳< : (d : Condition Ref) → Framing d 𝟏 d
  >[ d ]╳< = focus [ d ]╳
  -- focus on the one Ref in the middle and whatever is focused on the right
  infixr -1 >[_]&[_]⨾[_]⨾⨾>_
  >[_]&[_]⨾[_]⨾⨾>_ :
    ∀ (l : Condition Ref)
    (v : Ref) {ℓ} {A : Set ℓ} {x : A}
    (r : Condition Ref) {f d : Condition Ref} →
    Framing (l & r) f d →
    Framing (l & v ↦ x ⨾ r) (v ↦ x ⨾ f) d
  >[ l ]&[ v ]⨾[ r ]⨾⨾> focus p = focus ([ l ]&[ v ]⨾[ r ]⨾⨾ p)


  -- rewrite the input to a Framing
  substFraming : {o₁ o₂ i d : Condition Ref} → o₁ ≡ω₀ o₂ → Framing o₁ i d → Framing o₂ i d
  substFraming reflω₀ p = p

  -- more complicated introduction rules for Framing, which improve on the
  -- Restructuring operations because they track the discards where the discards
  -- function might get stuck evaluating

  -- discard whatever is to the left and focus as directed to on the right
  infixr 0 _&>_
  _&>_ : {r f d : Condition Ref} (l : Condition Ref) → Framing r f d → Framing (l & r) f (l & d)
  l &> focus [ discards ]╳           = >[ l & discards ]╳<
  l &> focus ([ m ]&[ v ]⨾[ r ]⨾⨾ p) =
      substFraming (assoc& l m (v ⨾⨾ r))
        (>[ l & m ]&[ v ]⨾[ r ]⨾⨾> substFraming (symω₀ (assoc& l m r)) (l &> focus p))
  -- discard whatever is to the right and focus as directed to on the left
  infixl 0 _<&_
  _<&_ : {l f d : Condition Ref} → Framing l f d → (r : Condition Ref) → Framing (l & r) f (d & r)
  focus [ discards ]╳           <& r = >[ discards & r ]╳<
  focus ([ l ]&[ v ]⨾[ m ]⨾⨾ p) <& r =
    substFraming (symω₀ (assoc& l (v ⨾⨾ m) r))
      (>[ l ]&[ v ]⨾[ m & r ]⨾⨾> substFraming (assoc& l m r) (focus p <& r))

  -- focus on the whole of a Condition
  >[_]< : (cond : Condition Ref) → Framing cond cond 𝟏
  >[ 𝟏         ]< = >[ 𝟏 ]╳<
  >[ v ⨾⨾ cond ]< = >[ 𝟏 ]&[ v ]⨾[ cond ]⨾⨾> >[ cond ]<
  -- "focus" on the 𝟏 in any Condition
  >𝟏< : {cond : Condition Ref} → Framing cond 𝟏 cond
  >𝟏< = >[ _ ]╳<
  -- focus on the whole of a Condition after rewriting it
  >[!_!]< : {pre post : Condition Ref} → pre ≡ω₀ post → Framing pre post 𝟏
  >[! reflω₀ !]< = >[ _ ]<

  -- put Framings in sequence, feeding the discards of one into the input of the
  -- next, and taking the conjunction of their outputs.
  infixr 1 _<&>_
  _<&>_ :
    {outer first middle second side : Condition Ref} →
    Framing outer first middle → Framing middle second side → Framing outer (first & second) side
  focus [ outer ]╳              <&> q = q
  focus ([ l ]&[ v ]⨾[ r ]⨾⨾ p) <&> q = >[ l ]&[ v ]⨾[ r ]⨾⨾> focus p <&> q

  -- _&>_, _<&_, >[_]<, and _<&>_ are useful for writing `Framing` proofs both by
  -- hand and automatically (see Imperative.Solvers)

  -- unfocus downgrades a Framing to a Restructuring that discards its discards
  -- alternatively, get a Restructuring that puts the discards on the side
  cancelFraming : {o i d : Condition Ref} → Framing o i d → Restructuring o (i & d)
  cancelFraming (focus [ discards ]╳)           = [ discards ]∎
  cancelFraming (focus ([ l ]&[ v ]⨾[ r ]⨾⨾ p)) = [ l ]&[ v ]⨾[ r ]⨾⨾ cancelFraming (focus p)
