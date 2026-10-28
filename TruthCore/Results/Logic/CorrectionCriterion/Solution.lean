import TruthCore.Logic.CorrectionCriterion

namespace TruthCore.Results.Logic.CorrectionCriterion
open TruthCore.Logic.CorrectionCriterion

/-- Exact extensional classification is equivalent to invariance under
identical data. Both nonconstant-norm controls are included. This proves no
criterion's justification and settles no private-language or truth theory. -/
theorem characterization : CriterionCharacterizationAndControls := by
  have factor : CriterionCharacterization := by
    intro State Evidence observe Correct
    constructor
    · rintro ⟨criterion, h⟩ s t same
      calc
        Correct s ↔ criterion (observe s) := (h s).symm
        _ ↔ criterion (observe t) := by rw [same]
        _ ↔ Correct t := h t
    · intro invariant
      refine ⟨(fun e => ∃ s, observe s = e ∧ Correct s), ?_⟩
      intro t
      constructor
      · rintro ⟨s, same, correct⟩
        exact (invariant s t same).mp correct
      · intro correct
        exact ⟨t, rfl, correct⟩
  refine ⟨factor, rfl, ?_, ?_⟩
  · intro h
    have invariant := (factor Bool (Bool × Bool)
      (fun _ => (true, true)) (fun s => s = true)).mp h
    have bad : false = true := (invariant false true rfl).mpr rfl
    cases bad
  · exact ⟨(fun s => s = true), fun _ => Iff.rfl⟩

end TruthCore.Results.Logic.CorrectionCriterion
