import TruthCore.Logic.CartesianFloor
import TruthCore.Results.Logic.TruthPilot.SomePropositionHolds.Solution
namespace TruthCore.Results.Logic.CartesianFloor
open TruthCore.Logic.CartesianFloor

/-- Constructive, with no classical axioms. -/
theorem nonContradiction : NonContradiction := by
  intro p h
  exact h.2 h.1

/-- The proposition False is a counterexample to universal truth. -/
theorem somePropositionFails : SomePropositionFails := by
  exact ⟨False, fun h => h⟩

/-- Compose the witnessed failure rather than postulate it. -/
theorem notEveryPropositionHolds : NotEveryPropositionHolds := by
  intro hAll
  obtain ⟨p, hp⟩ := somePropositionFails
  exact hp (hAll p)

end TruthCore.Results.Logic.CartesianFloor
