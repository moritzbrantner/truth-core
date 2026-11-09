module

public import TruthCore.Logic.ObjectiveTruthDefinitionFork

/-!
# Scoped internal counterfactual controls

Analyst test framework for the internal assertion question, not a completed
interpretation of MIND_INDEPENDENT_1 or metaphysical MIND_INDEPENDENT_2.
The supplied alternatives must represent relevant changes of approval while
holding the action fixed. Their adequacy and counterfactual selection remain
open. In particular this universal supplied-profile test is not automatically
a closest-world counterfactual. Assertion and licensing are primitive practice
data, indexed by attitudes; licensing is not actual truth or facthood.

Connection target: the named fixed-assessor approval account's failure premise
on the goodness/root route. These controls prevent replacing that substantive
premise with mere internal assertion or with a truth-profile calibration.
-/

@[expose] public section
namespace TruthCore.Metaethics.InternalCounterfactual

open TruthCore.Logic.ObjectiveTruthDefinitionFork

/-- One fixed moral content, with explicitly selected changed-approval profiles.
`asserts` records assertion of the counterfactual sentence, not the base content.
`licenses` records attitude-judged legitimacy of that assertion. Neither field
asserts successful quasi-realist vindication or supplies moral facts. -/
structure Frame where
  truth : TruthCore.Logic.ObjectiveTruthDefinitionFork.Frame
  content : truth.Sentence
  alternatives : truth.AttitudeProfile → Prop
  asserts : truth.AttitudeProfile → Prop
  licenses : truth.AttitudeProfile → Prop

/-- Explicit-profile candidate truth test; actual wrongness plus wrongness
through the supplied alternatives. No ontic independence is inferred. -/
def Counterfactual (f : Frame) : Prop :=
  f.truth.holds f.truth.actual f.content ∧
    ∀ p, f.alternatives p → f.truth.holds p f.content

/-- A practice asserts and licenses the sentence at its actual attitude. -/
def InternalAcceptance (f : Frame) : Prop :=
  f.asserts f.truth.actual ∧ f.licenses f.truth.actual

/-- Actual wrongness, a genuinely changed alternative, and attitude-sensitive
licensing coexist with acceptance of a false candidate counterfactual. -/
def acceptedFalse : Frame where
  truth := actualStable
  content := .actualTrueVariable
  alternatives := fun p => p = true
  asserts := fun _ => True
  licenses := fun p => p = false

/-- A true candidate counterfactual need not be asserted or licensed. -/
def unacceptedTrue : Frame where
  truth := actualStable
  content := .stableTrue
  alternatives := fun p => p = true
  asserts := fun _ => False
  licenses := fun p => p = true

/-- Nonvacuous separation in these explicit finite profiles only. This does
not refute quasi-realism or certify any metaphysical independence relation. -/
def Controls : Prop :=
  (InternalAcceptance acceptedFalse ∧ ¬ Counterfactual acceptedFalse ∧
    acceptedFalse.truth.holds false acceptedFalse.content ∧
    acceptedFalse.alternatives true ∧
    ¬ acceptedFalse.truth.holds true acceptedFalse.content ∧
    ¬ acceptedFalse.licenses true) ∧
  (Counterfactual unacceptedTrue ∧ ¬ InternalAcceptance unacceptedTrue ∧
    unacceptedTrue.alternatives true ∧ ¬ unacceptedTrue.licenses false)

end TruthCore.Metaethics.InternalCounterfactual
