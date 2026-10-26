import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.Quantifiers
import TruthCore.Logic.Configuration

namespace TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.JointToIndividual
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
open TruthCore.Modal

/-- Stipulated quantifier consequence; all frame, domain, presence and world parameters are shared explicitly. No metaphysical premise is discharged. -/
theorem checks {W I : Type} (F : Frame W) (present : I → W → Prop) (w : W)
    (h0 : JointAbsence F present w)
    : IndividualContingency F present w := by
  sorry
end TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.JointToIndividual
