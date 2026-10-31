import TruthCore.Causality.ContingentTotalityCause

namespace TruthCore.Results.Causality.ContingentTotalityCause
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.PossibleCauseOfContingency
open TruthCore.Causality.ContingentTotalityCause

/-- Conditional typed connection only: coverage and an actual outside-parts
cause yield a necessary cause of the same whole. No whole-level cause is
inferred from member-level causal laws. -/
theorem necessaryCause {W B : Type} [PartialOrder B]
    (s : Scenario W B) (w : W) (whole : B)
    (hCover : ContingentsCovered s w whole)
    (hCause : ExternalWholeCause s w whole) :
    NecessaryWholeCause s w whole := by
  sorry


/-- Connect the same typed totality route to the shared actual necessary-being
interface. The stronger necessaryCause theorem additionally retains causation. -/
theorem necessaryBeing {W B : Type} [PartialOrder B]
    (s : Scenario W B) (w : W) (whole : B)
    (hCover : ContingentsCovered s w whole)
    (hCause : ExternalWholeCause s w whole) :
    NecessaryBeing s.ontic w := by
  sorry

end TruthCore.Results.Causality.ContingentTotalityCause
