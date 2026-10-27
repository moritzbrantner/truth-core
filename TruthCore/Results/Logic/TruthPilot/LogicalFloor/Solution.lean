import TruthCore.Logic.TruthPilot
namespace TruthCore.Results.Logic.TruthPilot.LogicalFloor
open TruthCore.Logic.TruthPilot

/-- Constructive non-contradiction: a proof of `P ∧ ¬ P` refutes itself. -/
theorem nonContradiction : NonContradiction := by
  intro P h
  exact h.2 h.1

/-- `False` is a proposition that fails. -/
theorem somePropositionFails : SomePropositionFails := by
  exact ⟨False, fun h => h⟩

/-- Compose the witnessed failure: universal holding would prove `False`. -/
theorem notEveryPropositionHolds : NotEveryPropositionHolds := by
  intro hAll
  obtain ⟨P, hP⟩ := somePropositionFails
  exact hP (hAll P)

end TruthCore.Results.Logic.TruthPilot.LogicalFloor
