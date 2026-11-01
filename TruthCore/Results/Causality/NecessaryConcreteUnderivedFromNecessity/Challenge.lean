import TruthCore.Causality.NecessaryConcreteUnderived
import TruthCore.Logic.ExcludedMiddle

namespace TruthCore.Results.Causality.NecessaryConcreteUnderivedFromNecessity
open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Logic (ExcludedMiddle)

/-- Assembly on the concrete subtype. The underived witness may differ from
that supplied by hNecessary. Support exclusion is concrete-only at ALL admitted
worlds; the necessary-support union also ranges over ALL admitted worlds.
The additional support/frame policies remain open, not inferred from NE. -/
theorem underived {W B : Type} (m : Profile W B) (w : W)
    (hNecessary : NecessaryConcreteAt m w)
    (hRef : ActualReflexive m.ontic w)
    (hNoCont : NoContingentConcreteSupport m w)
    (hUnion : ConcreteNecessaryUnionWF m w)
    (hEM : ExcludedMiddle) : NecessaryConcreteUnderivedAt m w := by
  sorry

end TruthCore.Results.Causality.NecessaryConcreteUnderivedFromNecessity
