import TruthCore.Modal.DResearch.Laws

namespace TruthCore.Modal.DResearch
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite (Model eval)
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)
open TruthCore.Modern.Hume.Conceivability (Contingent)

/-- A serial two-cycle with no self-edges. Every atom of the fixed Unit
language is true at both labels. The states remain distinct Lean values. -/
def cycle : Model Bool Unit where
  worlds := [false, true]
  complete := by
    intro w
    cases w with
    | false => exact .head _
    | true => exact .tail _ (.head _)
  edge := fun w v => !w == v
  atom := fun _ _ => true

/-- Exact fixed-language denotations; no identity predicate is silently added. -/
def cycleLanguage : Domain Bool := expressible cycle.frame cycle.valuation

/-- Serial fixed-language collapse can be non-reflexive. Full-predicate
collapse is false at both labels; adding the separating predicate detects it.
The language is negation-closed but not world-extensional. -/
def LanguageChecks : Prop :=
  Serial cycle.frame ∧ (∀ w, ¬ cycle.frame.access w w) ∧
  (∀ w, MC cycle.frame cycleLanguage w) ∧
  Dia cycle.frame (MC cycle.frame cycleLanguage) false ∧
  Box cycle.frame (MC cycle.frame cycleLanguage) false ∧
  (∀ w, ¬ MC cycle.frame allPredicates w) ∧
  ¬ IdentityAdmissible cycleLanguage false ∧
  ¬ PropositionalExtensionality cycleLanguage ∧
  (∀ P, cycleLanguage P → cycleLanguage (fun w => ¬ P w)) ∧
  (∀ p : Formula Unit,
    Holds cycle.frame cycle.valuation false p ↔
    Holds cycle.frame cycle.valuation true p) ∧
  (∀ p : Formula Unit,
    ¬ Contingent cycle.frame (fun w => Holds cycle.frame cycle.valuation w p) false) ∧
  (Dia cycle.frame (fun w => w = true) false ∧ (false : Bool) ≠ true) ∧
  eval cycle false (.atom ()) = true ∧
  eval cycle false (.box (.atom ())) = true ∧
  eval cycle false (.diamond (.atom ())) = true

#guard eval cycle false (.atom ()) == true
#guard eval cycle true (.atom ()) == true
#guard eval cycle false (.box (.atom ())) == true
#guard eval cycle false (.diamond (.atom ())) == true
#guard cycle.edge false false == false
#guard cycle.edge true true == false
end TruthCore.Modal.DResearch
