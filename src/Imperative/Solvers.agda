{-# OPTIONS --safe #-}
module Imperative.Solvers where

open import Agda.Builtin.Reflection using (Telescope)
open import Agda.Primitive
open import Data.Bool
open import Data.List as List
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product
open import Data.Unit
open import Reflection renaming (normalise to normalize)

import Imperative.Condition
import Imperative.Framing
import Imperative.Restructuring

private
  allMetas : Term → List Meta
  allMetasArgs : List (Arg Term) → List Meta
  allMetasClauses : List Clause → List Meta
  allMetasTelescope : Telescope → List Meta
  allMetasArgs []             = []
  allMetasArgs (arg _ t ∷ as) = allMetas t ++ allMetasArgs as
  allMetasClauses []                                   = []
  allMetasClauses (Clause.clause        tel ps t ∷ cs) = allMetasTelescope tel ++ allMetas t ++ allMetasClauses cs
  allMetasClauses (Clause.absurd-clause tel ps   ∷ cs) = allMetasTelescope tel ++ allMetasClauses cs
  allMetasTelescope []                    = []
  allMetasTelescope ((_ , arg _ t) ∷ tel) = allMetas t ++ allMetasTelescope tel
  allMetas (var _ args) = allMetasArgs args
  allMetas (con _ args) = allMetasArgs args
  allMetas (def _ args) = allMetasArgs args
  allMetas (lam v (abs _ t)) = allMetas t
  allMetas (pat-lam cs args) = allMetasClauses cs ++ allMetasArgs args
  allMetas (pi (arg _ a) (abs _ b)) = allMetas a ++ allMetas b
  allMetas (agda-sort (Sort.set t)) = allMetas t
  allMetas (agda-sort (Sort.prop t)) = allMetas t
  allMetas (lit (meta m)) = m ∷ []
  allMetas (meta m args) = m ∷ allMetasArgs args
  allMetas _ = []

  Blocker′ : Set lzero
  Blocker′ = Maybe Blocker
  blockerTerm′ : Term → Blocker′
  blockerTerm′ t with allMetas t
  ... | []         = nothing
  ... | ms@(_ ∷ _) = just (blockerAny (List.map blockerMeta ms))
  blockerAll′ : List Blocker → Blocker′
  blockerAll′ []         = nothing
  blockerAll′ bs@(_ ∷ _) = just (blockerAll bs)
  blockTC′ : Blocker′ → TC ⊤
  blockTC′ nothing  = pure tt
  blockTC′ (just b) = blockTC b

  record ConditionPart : Set where
    field
      key : Term
      body : Term
  open ConditionPart

  conditionPartErr : ConditionPart → List ErrorPart
  conditionPartErr p =
    strErr "condition fragment (key " ∷ termErr (p .key) ∷ strErr ") " ∷
    termErr (p .body) ∷ []
  listErr : List (List ErrorPart) → List ErrorPart
  listErr []       = strErr "[]" ∷ []
  listErr (x ∷ xs) = strErr "[" ∷ x ++ loop xs
    where
      loop : List (List ErrorPart) → List ErrorPart
      loop []       = strErr "]" ∷ []
      loop (x ∷ xs) = strErr ", " ∷ x ++ loop xs

  record ListZipper {ℓ} (A : Set ℓ) : Set ℓ where
    constructor listZipper
    field
      before : List A
      focus : A
      after : List A
  infixr 5 _∷ᶻ_
  _∷ᶻ_ : ∀ {ℓ} {A : Set ℓ} → A → ListZipper A → ListZipper A
  x ∷ᶻ listZipper before focus after = listZipper (x ∷ before) focus after

  findMatches : List ConditionPart → Term → TC (List (ListZipper ConditionPart))
  findMatches []       k = pure []
  findMatches (p ∷ ps) k = do
    here ← catchTC (runSpeculative (unify (p .key) k >> pure (listZipper [] p ps ∷ [] , false))) (pure [])
    there ← findMatches ps k
    pure (here ++ List.map (p ∷ᶻ_) there)
  findMatch : List ConditionPart → ConditionPart → TC (List ConditionPart × List ConditionPart)
  findMatch ps q = findMatches ps (q .key) >>= λ where
    [] → typeError (
      strErr "no match for key " ∷ termErr (q .key) ∷
      strErr " in " ∷ listErr (List.map conditionPartErr ps))
    (listZipper before p after ∷ []) → do
      unify (p .body) (q .body)
      pure (before , after)
    _ → typeError (
      strErr "multiple matches for key " ∷ termErr (q .key) ∷
      strErr " in " ∷ listErr (List.map conditionPartErr ps))

  -- Definitions in Imperative.{Condition,Restructuring,Framing} have three
  -- arguments for the state thread type, the array type, and the current state
  -- thread. These are shorthands to skip those arguments while analyzing or
  -- building terms.
  pattern ctxArgs as = _ ∷ _ ∷ _ ∷ as
  defCtxArgs : List (Arg Term)
  defCtxArgs = vArg unknown ∷ vArg unknown ∷ hArg unknown ∷ []

  decomposeCondition : Term → TC (List ConditionPart × Blocker′)
  decomposeCondition conditionTerm = do
    conditionNormalized ← normalize conditionTerm
    parts ← peel conditionNormalized
    let keys = List.map key parts
    debugPrint "imperative.decomposeCondition" 10 (
      strErr "found keys: " ∷
      listErr (List.map (λ k → termErr k ∷ []) keys))
    pure (parts , blockerAll′ (mapMaybe blockerTerm′ keys))
    where
      peel : Term → TC (List ConditionPart)
      peel (con (quote Imperative.Condition.𝟏) (ctxArgs [])) = pure []
      peel (con (quote Imperative.Condition._⨾_) (ctxArgs (arg _ assignmentTerm ∷ arg _ rest ∷ []))) = do
        restParts ← peel rest
        key ← normalize (def (quote Imperative.Condition.Assignment.var) (vArg assignmentTerm ∷ []))
        pure (
          record {
            key = key;
            body = con
              (quote Imperative.Condition._⨾_)
              (vArg assignmentTerm ∷ vArg (con (quote Imperative.Condition.𝟏) []) ∷ [])
          } ∷
          restParts)
      peel t = pure (record { key = t; body = t } ∷ [])

  composeCondition : List ConditionPart → Term
  composeCondition []                    =
    con (quote Imperative.Condition.𝟏) []
  composeCondition (p ∷ ps) =
    def (quote Imperative.Condition._&_) (defCtxArgs ++ vArg (p .body) ∷ vArg (composeCondition ps) ∷ [])

  restructure-loop : List ConditionPart → List ConditionPart → Term → TC ⊤
  restructure-loop inputParts []       hole =
    unify hole (con (quote Imperative.Restructuring.[_]╳) (vArg (composeCondition inputParts) ∷ []))
  restructure-loop inputParts (p ∷ ps) hole = do
    before , after ← findMatch inputParts p
    subhole ← checkType unknown unknown
    unify hole
      (def (quote Imperative.Restructuring.[_]&[_]&[_]⨾⨾_) (
        defCtxArgs ++
        vArg (composeCondition before) ∷ vArg (p .body) ∷ vArg (composeCondition after) ∷
        vArg subhole ∷ []))
    restructure-loop (before ++ after) ps subhole

restructuring-tactic : Term → TC ⊤
restructuring-tactic hole = do
  input ← checkType unknown unknown
  output ← checkType unknown unknown
  checkType hole
    (def (quote Imperative.Restructuring.Restructuring) (defCtxArgs ++ vArg input ∷ vArg output ∷ []))

  inputParts , blocker1 ← decomposeCondition input
  debugPrint "imperative.restructuring-tactic" 20 (strErr "input: " ∷ listErr (List.map conditionPartErr inputParts))
  outputParts , blocker2 ← decomposeCondition output
  debugPrint "imperative.restructuring-tactic" 20 (strErr "output: " ∷ listErr (List.map conditionPartErr inputParts))
  blockTC′ (blockerAll′ (catMaybes (blocker1 ∷ blocker2 ∷ [])))

  debugPrint "imperative.restructuring-tactic" 10 (strErr "input: " ∷ listErr (List.map conditionPartErr inputParts))
  debugPrint "imperative.restructuring-tactic" 10 (strErr "output: " ∷ listErr (List.map conditionPartErr inputParts))
  restructure-loop inputParts outputParts hole
macro
  restructuring! : Term → TC ⊤
  restructuring! = restructuring-tactic

framing-tactic : Term → TC ⊤
framing-tactic hole = do
  subhole ← checkType unknown unknown
  unify hole (con (quote Imperative.Framing.focus) (vArg subhole ∷ []))
  restructuring-tactic subhole
macro
  framing! : Term → TC ⊤
  framing! = framing-tactic
