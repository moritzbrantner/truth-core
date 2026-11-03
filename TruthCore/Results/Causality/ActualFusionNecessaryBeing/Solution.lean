import TruthCore.Causality.ActualFusionNecessaryBeing

namespace TruthCore.Results.Causality.ActualFusionNecessaryBeing
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.ActualFusionNecessaryBeing
open TruthCore.Mereology.FusionNoNecessaryParts

/-- Five explicit actual fusion/part/causal inputs yield SOME actual necessary
being. The selected cause is not asserted necessary; no source truth follows. -/
theorem necessaryBeing {W B : Type} [PartialOrder B] (m : Ontic W B) (w : W)
    (sum : B) (hFusion : ActualFusionAt m w sum)
    (hParts : ActualPartsExistAt m w)
    (hCausal : ActualNoNecessaryPartsHaveCausesAt m w)
    (hActual : CausesHaveActualEndpointsAt m w)
    (hNonoverlap : CauseEffectNonoverlapAt m w) : NecessaryBeing m w := by
  apply Classical.byContradiction
  intro hNone
  have hNoParts : ∀ x, m.ExistsAt w x → NoNecessaryPartsAt m w x := by
    intro x hx p hpx hpNecessary
    exact hNone ⟨p, hParts x p hx hpx, hpNecessary⟩
  obtain ⟨c, hCause⟩ := hCausal sum hFusion.1 (hNoParts sum hFusion.1)
  have hcActual : m.ExistsAt w c := (hActual c sum hCause).1
  have hcPart : c ≤ sum := hFusion.2.1 c ⟨hcActual, hNoParts c hcActual⟩
  exact hNonoverlap c sum hCause ⟨c, le_refl c, hcPart⟩

end TruthCore.Results.Causality.ActualFusionNecessaryBeing
