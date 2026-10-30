import TruthCore.Logic.TruthNontriviality
import TruthCore.Results.Logic.TruthPilot.SomePropositionHolds.Solution
import TruthCore.Results.Logic.TruthPilot.LogicalFloor.Solution
namespace TruthCore.Results.Logic.TruthNontriviality.PropositionalCollapse
open TruthCore.Logic.TruthNontriviality
/-- Composes the two existing witnesses: a proposition that holds and one that
fails cannot be equivalent. About Lean's `Prop` only. -/
theorem noGlobalPropositionalCollapse : NoGlobalPropositionalCollapse := by
  intro hCollapse
  obtain ⟨P, hP⟩ := TruthCore.Results.Logic.TruthPilot.SomePropositionHolds.somePropositionHolds
  obtain ⟨Q, hQ⟩ := TruthCore.Results.Logic.TruthPilot.LogicalFloor.somePropositionFails
  exact hQ ((hCollapse P Q).1 hP)
end TruthCore.Results.Logic.TruthNontriviality.PropositionalCollapse
