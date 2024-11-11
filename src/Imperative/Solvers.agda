{-# OPTIONS --safe #-}
module Imperative.Solvers where

open import Agda.Builtin.Reflection using (Telescope; withReconstructed)
open import Agda.Primitive
open import Data.Bool
open import Data.List as List
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product as Σ
open import Data.Unit
open import Function
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
  allMetasArgs (arg (arg-info _ (modality irrelevant _)) t ∷ as) = allMetasArgs as
  allMetasArgs (arg _ t ∷ as) = allMetas t ++ allMetasArgs as
  allMetasClauses []                                   = []
  allMetasClauses (Clause.clause        tel ps t ∷ cs) = allMetasTelescope tel ++ allMetas t ++ allMetasClauses cs
  allMetasClauses (Clause.absurd-clause tel ps   ∷ cs) = allMetasTelescope tel ++ allMetasClauses cs
  allMetasTelescope []                    = []
  allMetasTelescope ((_ , arg _ t) ∷ tel) = allMetas t ++ allMetasTelescope tel
  allMetas (var _ args)              = allMetasArgs args
  allMetas (con _ args)              = allMetasArgs args
  allMetas (def _ args)              = allMetasArgs args
  allMetas (lam v (abs _ t))         = allMetas t
  allMetas (pat-lam cs args)         = allMetasClauses cs ++ allMetasArgs args
  allMetas (pi (arg _ a) (abs _ b))  = allMetas a ++ allMetas b
  allMetas (agda-sort (Sort.set t))  = allMetas t
  allMetas (agda-sort (Sort.prop t)) = allMetas t
  allMetas (lit (meta m))            = m ∷ []
  allMetas (meta m args)             = m ∷ allMetasArgs args
  allMetas _                         = []

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
  allMetasBlocker : Blocker → List Meta
  allMetasBlockers : List Blocker → List Meta
  allMetasBlocker (blockerAny bs) = allMetasBlockers bs
  allMetasBlocker (blockerAll bs) = allMetasBlockers bs
  allMetasBlocker (blockerMeta m) = m ∷ []
  allMetasBlockers []       = []
  allMetasBlockers (b ∷ bs) = allMetasBlocker b ++ allMetasBlockers bs
  allMetasBlocker′ : Blocker′ → List Meta
  allMetasBlocker′ nothing  = []
  allMetasBlocker′ (just b) = allMetasBlocker b

  record AtomicCondition : Set lzero where
    field
      key : Term
      body : Term
  open AtomicCondition
  infixr 0 _`&_
  data ConditionCode : Set lzero where
    `[_] : AtomicCondition → ConditionCode
    _`&_ : ConditionCode → ConditionCode → ConditionCode
  infixl 0 _<`&_
  infixr 0 _`&>_
  `𝟏 : AtomicCondition
  `𝟏 = record { key = code; body = code }
    where code = con (quote Imperative.Condition.𝟏) []
  blockerConditionCode′ : ConditionCode → Blocker′
  blockerConditionCode′ `[ atom ] = blockerTerm′ (key atom)
  blockerConditionCode′ (l `& r)  = blockerAll′ (catMaybes (blockerConditionCode′ l ∷ blockerConditionCode′ r ∷ []))

  -- context of an AtomicCondition in a ConditionCode
  data ∂ConditionCode/∂AtomicCondition : Set lzero where
    >`[-]< : ∂ConditionCode/∂AtomicCondition
    _<`&_  : ∂ConditionCode/∂AtomicCondition → ConditionCode → ∂ConditionCode/∂AtomicCondition
    _`&>_  : ConditionCode → ∂ConditionCode/∂AtomicCondition → ∂ConditionCode/∂AtomicCondition
  atomsInContext : ConditionCode → List (AtomicCondition × ∂ConditionCode/∂AtomicCondition)
  atomsInContext `[ a ]   = (a , >`[-]<) ∷ []
  atomsInContext (l `& r) =
    List.map (Σ.map₂ (_<`& r)) (atomsInContext l) ++ List.map (Σ.map₂ (l `&>_)) (atomsInContext r)
  -- corresponds to the discards of a Framing that has taken the atom focused by the context
  remainder : ∂ConditionCode/∂AtomicCondition → ConditionCode
  remainder >`[-]<    = `[ `𝟏 ]
  remainder (l <`& r) = remainder l `& r
  remainder (l `&> r) = l `& remainder r

  atomicConditionErr : AtomicCondition → List ErrorPart
  atomicConditionErr p =
    strErr "atomic condition (key " ∷ termErr (p .key) ∷ strErr ") " ∷
    termErr (p .body) ∷ []
  conditionCodeErr : ConditionCode → List ErrorPart
  conditionCodeErr `[ atom ] = atomicConditionErr atom
  conditionCodeErr (l `& r)  = strErr "(" ∷ conditionCodeErr l ++ strErr ") & (" ∷ conditionCodeErr r ++ strErr ")" ∷ []
  listErr : List (List ErrorPart) → List ErrorPart
  listErr []       = strErr "[]" ∷ []
  listErr (x ∷ xs) = strErr "[" ∷ x ++ loop xs
    where
      loop : List (List ErrorPart) → List ErrorPart
      loop []       = strErr "]" ∷ []
      loop (x ∷ xs) = strErr ", " ∷ x ++ loop xs

  pattern app𝟏 = con (quote Imperative.Condition.𝟏) (_ ∷ [])
  infixr 0 _app⨾_
  pattern _app⨾_ a c = con (quote Imperative.Condition._⨾_) (_ ∷ arg _ a ∷ arg _ c ∷ [])
  infix 1 _app↦_
  pattern _app↦_ r x = con (quote Imperative.Condition._↦_) (_ ∷ arg _ r ∷ _ ∷ _ ∷ arg _ x ∷ [])
  infixr 0 _app&_
  pattern _app&_ c d = def (quote Imperative.Condition._&_) (_ ∷ arg _ c ∷ arg _ d ∷ [])
  infix 1 _app↦＊_
  pattern _app↦＊_ s xs = def (quote Imperative.Condition._↦＊_) (_ ∷ _ ∷ arg _ s ∷ arg _ xs ∷ [])
  decomposeCondition : Term → TC ConditionCode
  decomposeCondition conditionTerm = do
    -- the normalized term may no longer typecheck (the culprit appears to be
    -- extended lambdas)
    -- hence just use it as structural recursion fuel while gently reducing the
    -- original term
    -- (relying on the hope that the terms that the user writes will type check)
    guide ← normalize conditionTerm
    debugPrint "imperative.decomposeCondition" 50 (strErr "decomposing " ∷ termErr conditionTerm ∷ [])
    debugPrint "imperative.decomposeCondition" 50 (strErr "with guide " ∷ termErr guide ∷ [])
    peel guide conditionTerm
    where
      mismatch : TC ConditionCode
      mismatch = typeError (strErr "normalized Condition does not match gently reduced Condition" ∷ [])
      peel : Term → Term → TC ConditionCode
      peel app𝟏                 original = do
        debugPrint "imperative.decomposeCondition" 60 (strErr "guide head 𝟏" ∷ [])
        pure `[ `𝟏 ]
      peel (_ app⨾ guide)       original = do
        debugPrint "imperative.decomposeCondition" 60 (strErr "guide head _⨾_" ∷ [])
        reduced ← reduce original
        debugPrint "imperative.decomposeCondition" 60 (strErr "WHNF: " ∷ termErr reduced ∷ [])
        case reduced of λ where
          (assignment app⨾ rest) → do
            reducedAssignment ← reduce assignment
            debugPrint "imperative.decomposeCondition" 60 (strErr "Assignment WHNF: " ∷ termErr reducedAssignment ∷ [])
            let singleton = con (quote Imperative.Condition._⨾_) (vArg reducedAssignment ∷ vArg (body `𝟏) ∷ [])
            ref ←
              case reducedAssignment of λ where
                (ref app↦ _) → pure ref
                _            → typeError (strErr "Assignment in WHNF not headed by _↦_" ∷ [])
            `rest ← peel guide rest
            pure (`[ record { key = ref; body = singleton } ] `& `rest)
          _                     → mismatch
      peel (guideL app& guideR) original = do
        debugPrint "imperative.decomposeCondition" 60 (strErr "guide head _&_" ∷ [])
        reduced ← reduce original
        debugPrint "imperative.decomposeCondition" 60 (strErr "WHNF: " ∷ termErr reduced ∷ [])
        case reduced of λ where
          (l app& r) → do
            `l ← peel guideL l
            `r ← peel guideR r
            pure (`l `& `r)
          _&>_       → mismatch
      peel _                    original = do
        debugPrint "imperative.decomposeCondition" 60 (strErr "guide is atomic" ∷ [])
        reduced ← reduce original
        debugPrint "imperative.decomposeCondition" 60 (strErr "WHNF: " ∷ termErr reduced ∷ [])
        case reduced of λ where
          (slice app↦＊ _) → pure `[ record { key = slice; body = reduced } ]
          _                → pure `[ record { key = original; body = reduced } ]

  composeCondition : ConditionCode → Term
  composeCondition `[ atom ] = body atom
  composeCondition (l `& r)  =
    def (quote Imperative.Condition._&_) (vArg (composeCondition l) ∷ vArg (composeCondition r) ∷ [])
  composeFocusingFraming : AtomicCondition → ∂ConditionCode/∂AtomicCondition → List (List ErrorPart) × Term
  composeFocusingFraming focus >`[-]<      =
    (strErr "giving >[_]< with focus " ∷ termErr (focus .body) ∷ []) ∷ [] ,
    def (quote Imperative.Framing.>[_]<) (vArg (focus .body) ∷ [])
  composeFocusingFraming focus (ctx <`& `r) =
    let debug , rec = composeFocusingFraming focus ctx in
    let r = composeCondition `r in
    (strErr "giving _<&_ with discard " ∷ termErr r ∷ []) ∷ debug ,
    def (quote Imperative.Framing._<&_) (vArg rec ∷ vArg r ∷ [])
  composeFocusingFraming focus (`l `&> ctx) =
    let debug , rec = composeFocusingFraming focus ctx in
    let l = composeCondition `l in
    (strErr "giving _&>_ with discard " ∷ termErr l ∷ []) ∷ debug ,
    def (quote Imperative.Framing._&>_) (vArg l ∷ vArg rec ∷ [])

  matches : AtomicCondition → AtomicCondition → TC Bool
  matches a b = catchTC (runSpeculative (unify (a .key) (b .key) >> pure (true , false))) (pure false)
  mapTC_ : ∀ {ℓ} {A : Set ℓ} → (A → TC ⊤) → List A → TC ⊤
  mapTC_ f []       = pure tt
  mapTC_ f (x ∷ xs) = do
    f x
    mapTC_ f xs
  filterTC : ∀ {ℓ} {A : Set ℓ} → (A → TC Bool) → List A → TC (List A)
  filterTC keep? []       = pure []
  filterTC keep? (x ∷ xs) = do
    keepX? ← keep? x
    xs′ ← filterTC keep? xs
    pure (if keepX? then x ∷ xs′ else xs′)
  fillFramingForAtom : ConditionCode → AtomicCondition → Term → TC ConditionCode
  fillFramingForAtom availables (record { key = con (quote Imperative.Condition.𝟏) _ }) hole = do
    debugPrint "imperative.framing-tactic" 20 (strErr "giving >𝟏<" ∷ [])
    unify hole (def (quote Imperative.Framing.>𝟏<) [])
    pure availables
  fillFramingForAtom availables wanted                                                  hole = do
    fits ← filterTC (λ (available , _) → matches wanted available) (atomsInContext availables)
    case fits of λ where
      []                        →
        typeError (
          strErr "no match for " ∷ atomicConditionErr wanted ++
          strErr " in " ∷ conditionCodeErr availables)
      ((available , rest) ∷ []) → do
        let debugs , solution = composeFocusingFraming available rest
        mapTC_ (debugPrint "imperative.framing-tactic" 20) debugs
        unify hole solution
        pure (remainder rest)
      (_ ∷ _ ∷ _)               →
        typeError (
          strErr "multiple matches for " ∷ atomicConditionErr wanted ++
          strErr " in " ∷ conditionCodeErr availables)

  fillFraming : ConditionCode → ConditionCode → Term → TC ConditionCode
  fillFraming available `[ wanted ] hole = do
    debugPrint "imperative.framing-tactic" 20 (strErr "begin atom" ∷ [])
    available′ ← fillFramingForAtom available wanted hole
    debugPrint "imperative.framing-tactic" 20 (strErr "end atom" ∷ [])
    pure available′
  fillFraming available (`l `& `r)  hole = do
    debugPrint "imperative.framing-tactic" 20 (strErr "begin _<&>_" ∷ [])
    l ← checkType unknown unknown
    r ← checkType unknown unknown
    unify hole (def (quote Imperative.Framing._<&>_) (vArg l ∷ vArg r ∷ []))
    available′ ← fillFraming available `l l
    available′′ ← fillFraming available′ `r r
    debugPrint "imperative.framing-tactic" 20 (strErr "end _<&>_" ∷ [])
    pure available′′

framing-tactic : Term → TC ⊤
framing-tactic hole = do
  debugPrint "imperative.framing-tactic" 30 (strErr "analyzing goal" ∷ [])
  outer ← checkType unknown unknown
  inner ← checkType unknown unknown
  checkType hole
    (def (quote Imperative.Framing.Framing) (vArg outer ∷ vArg inner ∷ vArg unknown ∷ []))

  `outer ← decomposeCondition outer
  `inner ← decomposeCondition inner
  debugPrint "imperative.framing-tactic" 30 (strErr "checking for blockers" ∷ [])
  let blocker = blockerAll′ (catMaybes (blockerConditionCode′ `outer ∷ blockerConditionCode′ `inner ∷ []))
  blockTC′ blocker
  debugPrint "imperative.framing-tactic" 10 (strErr "outer: " ∷ conditionCodeErr `outer)
  debugPrint "imperative.framing-tactic" 10 (strErr "inner: " ∷ conditionCodeErr `inner)

  `discard ← fillFraming `outer `inner hole
  debugPrint "imperative.framing-tactic" 10 (strErr "solved, discarding: " ∷ conditionCodeErr `discard)
macro
  framing! : Term → TC ⊤
  framing! = framing-tactic

restructuring-tactic : Term → TC ⊤
restructuring-tactic hole = do
  subhole ← checkType unknown unknown
  unify hole (def (quote Imperative.Framing.unfocus) (vArg subhole ∷ []))
  framing-tactic subhole
macro
  restructuring! : Term → TC ⊤
  restructuring! = restructuring-tactic
