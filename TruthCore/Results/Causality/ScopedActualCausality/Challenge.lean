import TruthCore.Causality.ScopedActualCausality

namespace TruthCore.Results.Causality.ScopedActualCausality
open TruthCore.Causality.ScopedActualCausality
open TruthCore.Causality.AtomisticCausalSource
open TruthCore.Causality.WorldSourceRegress
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic (ExcludedMiddle)

/-- Structural projection; no independent causal premise is established. -/
theorem globalToSelected {W B : Type} (m : Ontic W B) (w : W)
    (hGlobal : LocalCausalPrinciple m) : SelectedActualCausalCoverage m w := by
  sorry

/-- Same NecessaryBeing conclusion and same four structural inputs plus EM;
only global causal coverage is replaced by selected-world coverage. -/
theorem necessaryBeing {W B : Type} (m : Ontic W B) (w : W)
    [PartialOrder (Actual m w)]
    (hPop : ObjectPopulation (Actual m w))
    (hAtomic : AtomicParts (Actual m w))
    (hCover : ConditionalCausedSimpleCover (actualGraph m w))
    (hNoOverlap : CauseEffectNonoverlap (actualGraph m w))
    (hEM : ExcludedMiddle) (hCoverage : SelectedActualCausalCoverage m w) :
    NecessaryBeing m w := by
  sorry

/-- Exact existing finite ontology: structural background plus nonvacuous
selected coverage, while the old global coverage fails. -/
theorem strictControl : StrictControl := by
  sorry

end TruthCore.Results.Causality.ScopedActualCausality
