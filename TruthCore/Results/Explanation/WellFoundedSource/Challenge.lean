import TruthCore.Explanation.WellFoundedSource

namespace TruthCore.Results.Explanation.WellFoundedSource

open TruthCore.Explanation.ExistencePSR
open TruthCore.Explanation.WellFoundedSource

/-- Conditional existence-PSR syllogism: explanation tokens need not be
efficient causes or independently certified sufficient explanations. -/
theorem checks {World Being : Type} (m : Model World Being) (w : World)
    (h0 : PopulatedAt m w)
    (h1 : ExistencePSR m)
    (h2 : WellFoundedCausesAt m w) :
    ExplainedSourceAt m w := by
  sorry

end TruthCore.Results.Explanation.WellFoundedSource
