import TruthCore.Causality.NecessaryRootUniqueness

namespace TruthCore.Results.Causality.NecessaryConcreteFromUniqueRoot
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootUniqueness

/-- Structural projection/transcription only: preserve the SAME actual necessary
concrete witness while forgetting selected-rootness and uniqueness. -/
theorem necessaryConcrete {W B : Type} (m : Profile W B) (w : W)
    (hRoot : UniqueNecessaryActualRootAt m w) : NecessaryConcreteAt m w := by
  obtain ⟨n, hr, hNec, _⟩ := hRoot
  exact ⟨n, hr.1.1, hr.1.2, hNec⟩

end TruthCore.Results.Causality.NecessaryConcreteFromUniqueRoot
