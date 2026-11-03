import TruthCore.Causality.NecessaryConcreteUnderived
import TruthCore.Logic.ExcludedMiddle
import TruthCore.Results.Causality.NecessarilyUnderived.PositiveUnion.Solution

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
  obtain ⟨b, hc, he, hn⟩ := hNecessary
  have hConcreteNE : TruthCore.German.Kant.CosmologicalInference.NecessaryBeing
      (concreteOntic m) w := ⟨⟨b, hc⟩, he, hn⟩
  obtain ⟨target, ht, htn, hu⟩ :=
    TruthCore.Results.Causality.NecessarilyUnderived.PositiveUnion.checks
      (concreteOntic m) (concreteSupport m) w hConcreteNE hRef hNoCont hUnion hEM
  refine ⟨target.val, target.property, ht, htn, ?_⟩
  intro v a ha hea hEdge
  exact hu v ⟨a, ha⟩ hea hEdge

end TruthCore.Results.Causality.NecessaryConcreteUnderivedFromNecessity
