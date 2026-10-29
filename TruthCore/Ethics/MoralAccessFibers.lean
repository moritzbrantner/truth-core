import TruthCore.Logic.CorrectionCriterion

/-!
Analyst's finite access tests for #703, not a formalization of an entire moral
account. The fixed question is whether deliberately killing an innocent person
in the case under consideration is prohibited. `prohibited` is a supplied answer,
not an inference from reports; false does not encode permission, justification,
or a reason to act. Unrestricted states are epistemic stress assignments, not
assertions of metaphysically possible worlds. In particular a categorical account
may exclude every false assignment to this question.

`basis` is the Boolean output of a *proposed* relevant-basis assessment, not a
measured natural fact or a normative truth oracle already available to an agent.
`NaturalBasis` deliberately exposes the constitutive bridge required to equate it
with prohibition. `SufficientBasis` exposes only one direction, without making the
normative connection causal. Neither bridge is attributed to Railton, Boyd,
Aquinas or Enoch. Their fallible mechanisms are discussed, with precise primary
locators, in docs/naturalistic-moral-realism.md, "Identical-evidence test".
-/
namespace TruthCore.Ethics.MoralAccessFibers
open TruthCore.Logic.CorrectionCriterion

structure State where
  report : Bool
  basis : Bool
  prohibited : Bool

/-- A conscience/consensus report, identical abstaining behavior, and identical
apparent deliberative success. These coarse data omit the proposed basis. -/
def outward (s : State) : Bool × Bool × Bool := (s.report, true, true)

def Prohibited (s : State) : Prop := s.prohibited = true

def enriched (s : State) : (Bool × Bool × Bool) × Bool := (outward s, s.basis)

/-- Open constitutive bridge, not established epistemic access to the basis. -/
def NaturalBasis (s : State) : Prop := s.prohibited = s.basis

/-- An openly supplied categorical prohibition for the fixed act description.
No derivation of that substantive norm is claimed. -/
def Categorical (s : State) : Prop := s.prohibited = true

/-- An openly supplied sufficient normative condition; no causal relation or
reverse implication is encoded. Stronger than a modest correlation alone. -/
def SufficientBasis (s : State) : Prop := s.basis = true → Prohibited s

def ThinControl : Prop := ¬ AdmitsCriterion outward Prohibited

def NaturalControl : Prop :=
  ¬ AdmitsCriterion (fun s : {s // NaturalBasis s} => outward s.val)
      (fun s => Prohibited s.val) ∧
  AdmitsCriterion (fun s : {s // NaturalBasis s} => enriched s.val)
      (fun s => Prohibited s.val)

def CategoricalControl : Prop :=
  AdmitsCriterion (fun s : {s // Categorical s} => outward s.val)
      (fun s => Prohibited s.val) ∧
  ∃ s : {s // Categorical s}, s.val.report = false ∧ Prohibited s.val

def SufficientControl : Prop :=
  (∀ s : {s // SufficientBasis s}, s.val.basis = true → Prohibited s.val) ∧
  ¬ AdmitsCriterion (fun s : {s // SufficientBasis s} => enriched s.val)
      (fun s => Prohibited s.val)

/-- Exact data-relative conclusions on four explicitly delimited model classes;
no probability, actual moral truth, knowledge or categorical reason is proved. -/
def Controls : Prop :=
  ThinControl ∧ NaturalControl ∧ CategoricalControl ∧ SufficientControl

end TruthCore.Ethics.MoralAccessFibers
