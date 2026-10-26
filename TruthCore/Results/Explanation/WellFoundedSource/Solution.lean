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
  exact psr_gives_explained_source m w h0 h1 h2

end TruthCore.Results.Explanation.WellFoundedSource
