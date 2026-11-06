module

public import TruthCore.Modal.ReasonResponseHistory
public import TruthCore.Results.Modal.ChoiceContext.Solution
public import TruthCore.Results.Logic.CorrectionCriterion.Solution

@[expose] public section

namespace TruthCore.Results.Modal.ReasonResponseHistory
open TruthCore.Modal.ReasonResponseHistory
open TruthCore.Modal.ChoiceContext
open TruthCore.Logic.CorrectionCriterion

/-- With the other complete table inputs fixed, unchanged acquisition output
lifts to unchanged action by the exact existing context-closure theorem. -/
theorem closure (acquire : Acquisition) (review external review' external' reason imposed : Bool)
    (same : acquire review external = acquire review' external') :
    run acquire review external reason imposed = run acquire review' external' reason imposed := by
  apply TruthCore.Results.Modal.ChoiceContext.sameContextSameAction
  exact ⟨same, rfl⟩

theorem signalSensitive (acquire : Acquisition) : SignalSensitive acquire := by
  intro review external
  unfold run record action input response
  cases acquire review external <;> decide

/-- A joint pair of explicit acquisition mechanisms, not arbitrary ownership
flags. Their common present data include the entire reason-response function. -/
theorem pairedControls :
    observe selfReview = observe externalBypass ∧
    action (observe selfReview).1 = action (observe externalBypass).1 ∧
    ReviewInfluence selfReview ∧ ¬ ExternalInfluence selfReview ∧
    ExternalInfluence externalBypass ∧ ¬ ReviewInfluence externalBypass := by
  refine ⟨rfl, rfl, ⟨true, ?_⟩, ?_, ⟨true, ?_⟩, ?_⟩
  · decide
  · rintro ⟨external, different⟩
    exact different rfl
  · decide
  · rintro ⟨review, different⟩
    exact different rfl

/-- Specialize the existing arbitrary-predicate factorization. AdmitsCriterion
here means exact extensional classification, not epistemic or moral warrant. -/
theorem classifierBoundary :
    ¬ AdmitsCriterion observe ReviewInfluence ∧
    ¬ AdmitsCriterion observe ExternalInfluence := by
  have factor := TruthCore.Results.Logic.CorrectionCriterion.characterization.1
  constructor
  · intro classified
    have invariant := (factor Acquisition PresentData observe ReviewInfluence).mp classified
    exact pairedControls.2.2.2.2.2
      ((invariant selfReview externalBypass pairedControls.1).mp pairedControls.2.2.1)
  · intro classified
    have invariant := (factor Acquisition PresentData observe ExternalInfluence).mp classified
    exact pairedControls.2.2.2.1
      ((invariant selfReview externalBypass pairedControls.1).mpr pairedControls.2.2.2.2.1)

theorem certificate : Certificate := by
  refine ⟨closure, signalSensitive, pairedControls, ?_, classifierBoundary, ?_, ?_⟩
  · intro P
    exact TruthCore.Results.Logic.CorrectionCriterion.characterization.1
      Acquisition PresentData observe P
  · exact ⟨fun data => ReviewInfluence data.2, fun _ => Iff.rfl⟩
  · intro acquire review external reason
    rfl

end TruthCore.Results.Modal.ReasonResponseHistory
