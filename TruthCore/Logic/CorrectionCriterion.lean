/-!
An analytical profile prompted by PI I.258 and I.265 (Anscombe translation,
verified witness WITTGENSTEIN-PI-PRIVATE-CRITERION-CONTEXT). This is not a
formalization attributed to Wittgenstein: a norm of correctness is a supplied
predicate; data do not define it. A criterion below is merely an extensional
Prop-valued classification, not a computable test, epistemic justification,
public convention, or proof that a private language is possible/impossible.
No existing causal-response or moral-correction vocabulary has this meaning.
-/
namespace TruthCore.Logic.CorrectionCriterion

/-- A supplied correctness norm admits an exact classification using only the
specified data. No correctness of those data, accessibility, decidability or
justification of the criterion is assumed. -/
def AdmitsCriterion {State Evidence : Type} (observe : State → Evidence)
    (Correct : State → Prop) : Prop :=
  ∃ criterion : Evidence → Prop, ∀ s, criterion (observe s) ↔ Correct s

/-- Correctness cannot vary between states represented by identical data. This
is a condition on a norm relative to a projection, not a definition of truth. -/
def FiberInvariant {State Evidence : Type} (observe : State → Evidence)
    (Correct : State → Prop) : Prop :=
  ∀ s t, observe s = observe t → (Correct s ↔ Correct t)

/-- For every state/evidence type and supplied norm, exact classification using
only the data exists iff correctness is invariant on equal-data fibers. -/
def CriterionCharacterization : Prop :=
  ∀ (State Evidence : Type) (observe : State → Evidence) (Correct : State → Prop),
    AdmitsCriterion observe Correct ↔ FiberInvariant observe Correct

/-- Two states share the complete pair of reports (`true`, `true`) while their
supplied correctness differs. No classifier on these reports can be exact.
Identity data do admit an exact classifier for the same nonconstant norm.
This is a finite omission control, not a sociological or private-language claim. -/
def CriterionControls : Prop :=
  let reports : Bool → Bool × Bool := fun _ => (true, true)
  let Correct : Bool → Prop := fun s => s = true
  reports false = reports true ∧
  ¬ AdmitsCriterion reports Correct ∧
  AdmitsCriterion (fun s : Bool => s) Correct

/-- The characterization and both explicit boundary controls. -/
def CriterionCharacterizationAndControls : Prop :=
  CriterionCharacterization ∧ CriterionControls

end TruthCore.Logic.CorrectionCriterion
