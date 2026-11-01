import TruthCore.Causality.NecessaryRootUniqueness

namespace TruthCore.Results.Causality.NecessaryConcreteFromUniqueRoot
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootUniqueness

theorem necessaryConcrete {W B : Type} (m : Profile W B) (w : W)
    (hRoot : UniqueNecessaryActualRootAt m w) : NecessaryConcreteAt m w := by
  sorry

end TruthCore.Results.Causality.NecessaryConcreteFromUniqueRoot
