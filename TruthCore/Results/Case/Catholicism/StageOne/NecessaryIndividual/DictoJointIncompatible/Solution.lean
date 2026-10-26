import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.Quantifiers
import TruthCore.Logic.Configuration

namespace TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.DictoJointIncompatible
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
open TruthCore.Modal

/-- Stipulated quantifier consequence; all frame, domain, presence and world parameters are shared explicitly. No metaphysical premise is discharged. -/
theorem checks {W I : Type} (F : Frame W) (present : I → W → Prop) (w : W)
    (h0 : DeDicto F present w)
    (h1 : JointAbsence F present w)
    : TruthCore.Logic.ConfigurationFalse := by
  obtain ⟨v, hv, hn⟩ := h1
  exact hn (h0 v hv)
end TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.DictoJointIncompatible
