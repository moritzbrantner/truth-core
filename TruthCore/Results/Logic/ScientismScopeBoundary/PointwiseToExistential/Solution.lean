module
public import TruthCore.Logic.ScientismScopeBoundary
@[expose] public section
namespace TruthCore.Results.Logic.ScientismScopeBoundary.PointwiseToExistential
open TruthCore.Logic.Scientism
open TruthCore.Logic.ScientismScopeBoundary
theorem pointwiseToExistential {Claim : Type} (E : EpistemicFrame Claim) (scope : Claim → Prop)
    (h : NonEmpiricalWitnessesInScope E scope) : SomeNonEmpiricalWitnessInScope E scope := by
  intro ⟨c, hEstablished, hNotEmpirical⟩
  exact ⟨c, h c hEstablished hNotEmpirical, hEstablished, hNotEmpirical⟩
end TruthCore.Results.Logic.ScientismScopeBoundary.PointwiseToExistential
