module
public import TruthCore.Results.Causality.CommonPriority.Solution
@[expose] public section
namespace TruthCore.Results.Causality.CommonPriority.ContingentGround
open TruthCore.Causality.CommonPriority
 theorem checks : NoContingentBoundary := by
  refine ⟨?_, union_to_rank _ _ _ TruthCore.Models.NecessarilyUnderived.switchingUnionWellFounded,
    TruthCore.Models.NecessarilyUnderived.switchingHasContingentGround,
    TruthCore.Models.NecessarilyUnderived.switchingNoUnderived⟩
  intro _ n hn v hv _
  exact hn v hv
end TruthCore.Results.Causality.CommonPriority.ContingentGround
