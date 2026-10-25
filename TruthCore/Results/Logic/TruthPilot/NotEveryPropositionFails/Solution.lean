import TruthCore.Logic.TruthPilot
import TruthCore.Results.Logic.TruthPilot.SomePropositionHolds.Solution
namespace TruthCore.Results.Logic.TruthPilot.NotEveryPropositionFails
open TruthCore.Logic.TruthPilot
/-- Compose the separately verified existential proof: universal failure would negate its witnessed proposition. -/
theorem notEveryPropositionFails : NotEveryPropositionFails := by
  intro hAllFail
  obtain ⟨P, hP⟩ := TruthCore.Results.Logic.TruthPilot.SomePropositionHolds.somePropositionHolds
  have hNotP := hAllFail P
  exact hNotP hP
end TruthCore.Results.Logic.TruthPilot.NotEveryPropositionFails
