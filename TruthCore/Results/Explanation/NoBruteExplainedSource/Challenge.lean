import TruthCore.Explanation.NoBruteExistence
import TruthCore.Explanation.WellFoundedSource
namespace TruthCore.Results.Explanation.NoBruteExplainedSource
open TruthCore.Explanation.ExistencePSR
open TruthCore.Explanation.NoBruteExistence
open TruthCore.Explanation.WellFoundedSource
/-- Local explanation coverage suffices; global existence-PSR is not required.
No explanatory-to-causal bridge or claim of adequate explanation is added. -/
theorem checks {World Being : Type} (m : Model World Being) (w : World)
    (hPop : PopulatedAt m w) (hLocal : NoBruteExistenceAt m w)
    (hWF : WellFoundedCausesAt m w) : ExplainedSourceAt m w := by
  sorry
end TruthCore.Results.Explanation.NoBruteExplainedSource
