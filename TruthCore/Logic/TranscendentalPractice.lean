import TruthCore.Logic.CorrectionCriterion
import TruthCore.Logic.ReflectiveCoherence

/-!
# Transcendental practice: access and agency boundaries

Two source-free semantic experiments reuse the certified correctness-criterion
and reflective-coherence frameworks. A truth-directed selection policy is a
normative constraint on selected worldviews, not an evidence-sensitive method
of identifying their true contents. Conversely, an exact extensional classifier
does not impose a norm on which worldviews to select. A chosen effective means
can be forced by *achieved* ends and unique efficacy, without a categorical
ought following from those descriptive conditions.

Neither experiment formalizes human epistemic competence, psychological
wishful thinking, objectively binding moral duties, or real-world metaphysics.
The finite controls are counterexamples to unqualified formal implications,
not evidence that the stipulated rival practices are actual or adequate.
-/

namespace TruthCore.Logic.TranscendentalPractice

open TruthCore.Logic.CorrectionCriterion
open TruthCore.Logic.ReflectiveCoherence

/-- Two independent requirements for truth-directed belief and correction.

* Exact evidence-based classification of a claim's truth must respect
  observational indistinguishability (the #Wittgenstein criterion theorem).
* A policy can select only actually true worldviews while a Boolean claim's
  truth is unclassifiable from constant reports.
* Identity reports can classify the same claim's truth even when a policy
  selects a false worldview. Neither property entails the other.

`STMT-TRANSCENDENTAL-INQUIRY-ACCESS-BOUNDARY` does not establish that such a
criterion is computable, warranted, or actually available to an inquirer. -/
def InquiryAccessBoundary : Prop :=
  (∀ (World Claim Evidence : Type) (S : Semantics World Claim)
      (observe : World → Evidence) (p : Claim),
    AdmitsCriterion observe (fun w => S.trueAt w p) →
      FiberInvariant observe (fun w => S.trueAt w p)) ∧
  (∃ select : Worldview Bool → Prop,
    TruthDirected twoWorldSemantics true select ∧
    select emptyWorldview ∧
    ¬ AdmitsCriterion (fun _ : Bool => (true, true))
      (fun w => twoWorldSemantics.trueAt w true)) ∧
  (AdmitsCriterion (fun w : Bool => w)
      (fun w => twoWorldSemantics.trueAt w true) ∧
    ¬ TruthDirected twoWorldSemantics true onlyDenier)

/-! ## Effective means and categorical oughts -/

/-- A minimal extensional profile of an end, performed actions and an interpreted
one-step efficacy relation. `effective a g` says that action `a` realizes goal
`g` *in this profile*: pressing a working button to open a dialog is an
illustration, pressing an unrelated button is a counterexample. The relation
has no assumed transitivity, time, causal mechanism, or metaphysical grounding.
`categoricalOught` is independent: successful realization is not a definition
of moral duty. This is not a theory of deliberation or responsibility. -/
structure GoalPractice (Goal Action : Type) where
  values : Goal → Prop
  performs : Action → Prop
  effective : Action → Goal → Prop
  categoricalOught : Action → Prop

/-- The end is valued and some performed action realizes it in this profile. Merely
intending it, recognizing a means, or having a reason is weaker. -/
def Realizes {Goal Action : Type} (P : GoalPractice Goal Action) (g : Goal) : Prop :=
  P.values g ∧ ∃ a, P.performs a ∧ P.effective a g

/-- The candidate action works, and no other effective action is available in
the interpreted action domain. This is uniqueness of efficacy, not a duty. -/
def OnlyEffective {Goal Action : Type} (P : GoalPractice Goal Action)
    (a : Action) (g : Goal) : Prop :=
  P.effective a g ∧ ∀ b, P.effective b g → b = a

/-- A one-goal, two-action practice: only `true` is performed and productive.
The parameter changes *only* the categorical-duty extension, so both finite
interpretations realize the same end by the same unique means. -/
def oneGoalPractice (duty : Bool) : GoalPractice Unit Bool where
  values _ := True
  performs a := a = true
  effective a _ := a = true
  categoricalOught a := duty = true ∧ a = true

/-- Success with one effective action requires its performance. But two
nonempty, otherwise identical successful practices disagree about a categorical
duty on that act. The latter is a joint finite omission witness, not proof of
the existence or nonexistence of objective moral obligations
(`STMT-TRANSCENDENTAL-AGENCY-DUTY-BOUNDARY`). -/
def AgencyDutyBoundary : Prop :=
  (∀ (Goal Action : Type) (P : GoalPractice Goal Action) (g : Goal) (a : Action),
    Realizes P g → OnlyEffective P a g → P.performs a) ∧
  (let obliged := oneGoalPractice true
   let unbound := oneGoalPractice false
   Realizes obliged () ∧ Realizes unbound () ∧
     OnlyEffective obliged true () ∧ OnlyEffective unbound true () ∧
     (∀ g, obliged.values g ↔ unbound.values g) ∧
     (∀ a, obliged.performs a ↔ unbound.performs a) ∧
     (∀ a g, obliged.effective a g ↔ unbound.effective a g) ∧
     obliged.categoricalOught true ∧ ¬ unbound.categoricalOught true)

end TruthCore.Logic.TranscendentalPractice
