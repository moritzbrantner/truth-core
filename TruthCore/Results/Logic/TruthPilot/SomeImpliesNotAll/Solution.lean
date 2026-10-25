import TruthCore.Logic.TruthPilot
namespace TruthCore.Results.Logic.TruthPilot.SomeImpliesNotAll
open TruthCore.Logic.TruthPilot
/-- Eliminate the existential witness and contradict universal failure. One direction of explicit reciprocal entailment. -/
theorem someImpliesNotAll (hSome : SomePropositionHolds) : NotEveryPropositionFails := by
  obtain ⟨P, hP⟩ := hSome
  intro hAllFail
  have hNotP := hAllFail P
  exact hNotP hP
end TruthCore.Results.Logic.TruthPilot.SomeImpliesNotAll
