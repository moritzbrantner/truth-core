module
public import TruthCore.Modal.RevisionUptake
@[expose] public section
namespace TruthCore.Results.Modal.RevisionUptake
open TruthCore.Modal.RevisionUptake

theorem screening : Screening := by
  refine ⟨?_, ?_, by decide⟩
  · intro gate override
    cases gate <;> cases override <;> unfold Participates revise <;> decide
  · intro acquire u m recommendation
    rfl

theorem controls : Controls := by
  unfold Controls
  exact ⟨by decide, by decide, by decide⟩
end TruthCore.Results.Modal.RevisionUptake
