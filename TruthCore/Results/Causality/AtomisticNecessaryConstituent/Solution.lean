import TruthCore.Causality.AtomisticCausalSource
import TruthCore.Causality.WorldSourceRegress
import TruthCore.Causality.ActualFusionNecessaryBeing
import TruthCore.Logic.ExcludedMiddle
import TruthCore.Results.Causality.AtomisticCausalSource.Solution
import TruthCore.Results.Causality.WorldSourceRegress.Solution

namespace TruthCore.Results.Causality.AtomisticNecessaryConstituent
open TruthCore.Causality.AtomisticCausalSource
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Causality.ActualFusionNecessaryBeing
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic (ExcludedMiddle)

/-- Non-corpus pointwise consumer: the SAME actual source has an ambient
necessary part. Causal endpoint soundness is needed because actual-sourcehood
excludes incoming ACTUAL candidates, not arbitrary absent carrier values. -/
theorem sourceHasNecessaryPart {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) (s : Actual m w)
    (hSource : (actualGraph m w).Source s) (hEM : ExcludedMiddle)
    (hCausal : ActualNoNecessaryPartsHaveCausesAt m w)
    (hActual : CausesHaveActualEndpointsAt m w) :
    ∃ p, p ≤ s.val ∧ NecessaryAt m w p := by
  cases hEM (∃ p, p ≤ s.val ∧ NecessaryAt m w p) with
  | inl hPart => exact hPart
  | inr hNoPart =>
    have hNoNecessaryParts :
        TruthCore.Mereology.FusionNoNecessaryParts.NoNecessaryPartsAt m w s.val :=
      fun p hp hNecessary => hNoPart ⟨p, hp, hNecessary⟩
    obtain ⟨c, hc⟩ := hCausal s.val s.property hNoNecessaryParts
    have hNoActualCause :=
      (TruthCore.Results.Causality.WorldSourceRegress.actualSource_iff m w s).mp hSource
    exact False.elim (hNoActualCause ⟨c, (hActual c s.val hc).1, hc⟩)

/-- Eight explicit inputs yield SOME actual necessary individual, possibly a
part of the selected actual source. The source itself is not asserted necessary.
The actual subtype inherits the supplied ambient parthood order. No activity,
modal reflexivity, global well-foundedness or no-necessary-parts cover is used. -/
theorem necessaryBeing {W B : Type} [PartialOrder B] (m : Ontic W B) (w : W)
    (hPop : ObjectPopulation (Actual m w))
    (hAtomic : AtomicParts (Actual m w))
    (hCover : ConditionalCausedSimpleCover (actualGraph m w))
    (hNoOverlap : CauseEffectNonoverlap (actualGraph m w))
    (hEM : ExcludedMiddle)
    (hCausal : ActualNoNecessaryPartsHaveCausesAt m w)
    (hActual : CausesHaveActualEndpointsAt m w)
    (hParts : ActualPartsExistAt m w) : NecessaryBeing m w := by
  obtain ⟨s, hSource⟩ := TruthCore.Results.Causality.AtomisticCausalSource.source
    (actualGraph m w) hPop hAtomic hCover hNoOverlap hEM
  obtain ⟨p, hp, hNecessary⟩ := sourceHasNecessaryPart m w s hSource hEM hCausal hActual
  exact ⟨p, hParts s.val p s.property hp, hNecessary⟩

end TruthCore.Results.Causality.AtomisticNecessaryConstituent
