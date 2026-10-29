import TruthCore.Modal.DeonticFutureBoundary

/-! Analyst finite controls for the concrete questions in #699. `Facts` fixes
case facts independently of any moral verdict. The finite assignments are not
attributed to historical theories or asserted metaphysically possible. -/
namespace TruthCore.Ethics.HardCaseTyped
open TruthCore.Modal.DeonticFutureBoundary

inductive Person | offender | victim deriving DecidableEq
inductive Act | violate | kill | keepPromise | preventHarm | abstain deriving DecidableEq
inductive Context | violation | killing | conflict deriving DecidableEq
inductive Good | promiseKeeping | harmPrevention deriving DecidableEq

/-- Case facts and feasible actions; `nonconsensual`, `innocent` and
`nonthreatening` are independently supplied factual predicates. -/
structure Facts where
  feasible : Context → Act → Prop
  actor : Act → Person
  target : Act → Person
  nonconsensual : Context → Act → Prop
  deliberateKilling : Context → Act → Prop
  innocent : Context → Person → Prop
  nonthreatening : Context → Person → Prop
  indifferent : Person → Prop
  benefits : Context → Person → Act → Prop
  unpunished : Context → Person → Act → Prop
  realizes : Context → Act → Good → Prop
  recognized : Context → Good → Prop

/-- No moral conclusion is built into either case description. -/
def HardCases (f : Facts) : Prop :=
  f.actor .violate = .offender ∧ f.target .violate = .victim ∧
  f.feasible .violation .violate ∧ f.nonconsensual .violation .violate ∧
  f.actor .kill = .offender ∧ f.target .kill = .victim ∧
  f.feasible .killing .kill ∧ f.deliberateKilling .killing .kill ∧
  f.innocent .killing .victim ∧ f.nonthreatening .killing .victim ∧
  f.indifferent .offender ∧
  f.benefits .violation .offender .violate ∧ f.unpunished .violation .offender .violate ∧
  f.benefits .killing .offender .kill ∧ f.unpunished .killing .offender .kill

/-- A valuation is supplied independently; absence of prohibition is not
permission. A reason here is a categorical reason against this action. -/
structure Verdict where
  forbidden : Context → Act → Prop
  reasonAgainst : Person → Context → Act → Prop

/-- The same facts admit opposite prohibitions, and even when both prohibitions
are supplied a categorical reason can vary. This excludes no richer theory. -/
def HardOmission : Prop :=
  ∃ (f : Facts) (yes no withReason withoutReason : Verdict), HardCases f ∧
    yes.forbidden .violation .violate ∧ yes.forbidden .killing .kill ∧
    ¬ no.forbidden .violation .violate ∧ ¬ no.forbidden .killing .kill ∧
    withReason.forbidden .violation .violate ∧ withReason.forbidden .killing .kill ∧
    withoutReason.forbidden .violation .violate ∧ withoutReason.forbidden .killing .kill ∧
    withReason.reasonAgainst .offender .violation .violate ∧
    withReason.reasonAgainst .offender .killing .kill ∧
    ¬ withoutReason.reasonAgainst .offender .violation .violate ∧
    ¬ withoutReason.reasonAgainst .offender .killing .kill

/-- Shared goods are independently represented: one action realizes promise
keeping only, the other serious harm prevention only. Both are feasible.
Two ideal frames with the same facts and availability make opposite duties,
with a feasible ideal successor in each. No numerical weights are assumed. -/
def ConflictOmission : Prop :=
  ∃ (f : Facts) (i₁ i₂ : TruthCore.Modal.Frame Act),
    f.recognized .conflict .promiseKeeping ∧ f.recognized .conflict .harmPrevention ∧
    f.realizes .conflict .keepPromise .promiseKeeping ∧
    ¬ f.realizes .conflict .keepPromise .harmPrevention ∧
    f.realizes .conflict .preventHarm .harmPrevention ∧
    ¬ f.realizes .conflict .preventHarm .promiseKeeping ∧
    f.feasible .conflict .keepPromise ∧ f.feasible .conflict .preventHarm ∧
    (∃ a, i₁.access .abstain a ∧ f.feasible .conflict a) ∧
    (∃ a, i₂.access .abstain a ∧ f.feasible .conflict a) ∧
    Ought i₁ .abstain (fun a => a = .keepPromise) ∧
    Ought i₂ .abstain (fun a => a = .preventHarm)

def Certificate : Prop := HardOmission ∧ ConflictOmission
end TruthCore.Ethics.HardCaseTyped
