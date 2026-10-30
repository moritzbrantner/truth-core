import TruthCore.Results.Explanation.NoBruteExistence.Solution
import TruthCore.Logic.Configuration
namespace TruthCore.Results.Explanation.NoBruteIncompatible
open TruthCore.Explanation.ExistencePSR
open TruthCore.Explanation.NoBruteExistence
/-- Selection-pruning interface for the bookkeeping incompatibility, with
both selected local positions listed explicitly. No EM premise is needed. -/
theorem checks {World Being : Type} (m : Model World Being) (w : World)
    (hNo : NoBruteExistenceAt m w) (hBrute : BruteExistenceAt m w) :
    TruthCore.Logic.ConfigurationFalse := by
  sorry
end TruthCore.Results.Explanation.NoBruteIncompatible
