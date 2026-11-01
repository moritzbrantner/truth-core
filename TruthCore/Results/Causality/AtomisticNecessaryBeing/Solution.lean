import TruthCore.Causality.AtomisticCausalSource
import TruthCore.Causality.WorldSourceRegress
import TruthCore.Results.Causality.AtomisticCausalSource.Solution
import TruthCore.Results.Causality.PossibleCausalSourceNecessity.Solution

namespace TruthCore.Results.Causality.AtomisticNecessaryBeing
open TruthCore.Causality.AtomisticCausalSource
open TruthCore.Causality.WorldSourceRegress
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic (ExcludedMiddle)

/-- Conditional complete-production interpretation on actual objects only.
No concreteness, grounding identity, activity or modal frame law is assumed. -/
theorem necessaryBeing {W B : Type} (m : Ontic W B) (w : W)
    [PartialOrder (Actual m w)]
    (hPop : ObjectPopulation (Actual m w))
    (hAtomic : AtomicParts (Actual m w))
    (hCover : ConditionalCausedSimpleCover (actualGraph m w))
    (hNoOverlap : CauseEffectNonoverlap (actualGraph m w))
    (hEM : ExcludedMiddle) (hCausal : LocalCausalPrinciple m) :
    NecessaryBeing m w := by
  obtain ⟨c, hc⟩ := TruthCore.Results.Causality.AtomisticCausalSource.source
    (actualGraph m w) hPop hAtomic hCover hNoOverlap hEM
  have hs := (TruthCore.Results.Causality.WorldSourceRegress.actualSource_iff m w c).mp hc
  exact ⟨c.val, c.property,
    TruthCore.Results.Causality.PossibleCausalSourceNecessity.source_necessary_at
      m w c.val hEM hCausal c.property hs⟩

end TruthCore.Results.Causality.AtomisticNecessaryBeing
