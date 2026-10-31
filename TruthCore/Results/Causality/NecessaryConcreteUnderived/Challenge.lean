import TruthCore.Causality.NecessaryConcreteUnderived

namespace TruthCore.Results.Causality.NecessaryConcreteUnderived

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- Compose actual contingent dependence with the modal union route on the
concrete subtype. No necessary witness is assumed as a fresh premise. The
conclusion excludes existing concrete supporters only, at all admitted worlds.
No premise here establishes its own metaphysical applicability. -/
theorem checks {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWF : ActualGroundingWF m w)
    (hDep : EveryContingentGroundedAt m w)
    (hRef : ActualReflexive m.ontic w)
    (hNoCont : NoContingentConcreteSupport m w)
    (hUnion : ConcreteNecessaryUnionWF m w)
    (hEM : ExcludedMiddle) :
    NecessaryConcreteUnderivedAt m w := by
  sorry

/-- Joint consistency control with a genuinely contingent concrete dependent. -/
theorem jointWitness : JointWitness := by
  sorry

end TruthCore.Results.Causality.NecessaryConcreteUnderived
