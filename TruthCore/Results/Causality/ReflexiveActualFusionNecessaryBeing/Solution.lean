import TruthCore.Causality.ActualFusionNecessaryBeing
import TruthCore.Causality.NecessarilyUnderived
import TruthCore.Explanation.WellFoundedSource

namespace TruthCore.Results.Causality.ReflexiveActualFusionNecessaryBeing
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.ActualFusionNecessaryBeing
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Explanation.ExistencePSR
open TruthCore.Explanation.WellFoundedSource (PopulatedAt)
open TruthCore.Mereology.FusionNoNecessaryParts

/-- Unregistered reductio tail. Necessity actualization is supplied explicitly
here; registered MF2 variants construct it directly from local reflexivity.
This is not a proof that reflexivity makes every actual object's parts actual. -/
theorem necessaryBeingOfActualizedNecessity {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) (sum : B) (hFusion : ActualFusionAt m w sum)
    (hActualize : ∀ p, NecessaryAt m w p → m.ExistsAt w p)
    (hCausal : ActualNoNecessaryPartsHaveCausesAt m w)
    (hActual : CausesHaveActualEndpointsAt m w)
    (hNonoverlap : CauseEffectNonoverlapAt m w) : NecessaryBeing m w := by
  apply Classical.byContradiction
  intro hNone
  have hNoParts : ∀ x, NoNecessaryPartsAt m w x := by
    intro x p _hpx hpNecessary
    exact hNone ⟨p, hActualize p hpNecessary, hpNecessary⟩
  obtain ⟨c, hCause⟩ := hCausal sum hFusion.1 (hNoParts sum)
  have hcActual : m.ExistsAt w c := (hActual c sum hCause).1
  have hcPart : c ≤ sum := hFusion.2.1 c ⟨hcActual, hNoParts c⟩
  exact hNonoverlap c sum hCause ⟨c, le_refl c, hcPart⟩

/-- Replace actual-part existence by selected-world reflexivity, with the
other four registered inputs unchanged. Output is SOME bare actual NE. -/
theorem necessaryBeing {W B : Type} [PartialOrder B] (m : Ontic W B) (w : W)
    (sum : B) (hFusion : ActualFusionAt m w sum)
    (hReflexive : ActualReflexive m w)
    (hCausal : ActualNoNecessaryPartsHaveCausesAt m w)
    (hActual : CausesHaveActualEndpointsAt m w)
    (hNonoverlap : CauseEffectNonoverlapAt m w) : NecessaryBeing m w := by
  exact necessaryBeingOfActualizedNecessity m w sum hFusion
    (fun p hp => hp w hReflexive) hCausal hActual hNonoverlap

/-- Existing owner population plus conditional selected-family formation,
local reflexivity and three causal policies. Model.explains remains unused;
no actual-part law, PSR or unconditional actual family/sum is assumed. -/
theorem fromPopulation {W B : Type} [PartialOrder B] (M : Model W B) (w : W)
    (hPopulation : PopulatedAt M w)
    (hFusion : ConditionalActualFusionAt M.ontic w)
    (hReflexive : ActualReflexive M.ontic w)
    (hCausal : ActualNoNecessaryPartsHaveCausesAt M.ontic w)
    (hActual : CausesHaveActualEndpointsAt M.ontic w)
    (hNonoverlap : CauseEffectNonoverlapAt M.ontic w) :
    NecessaryBeing M.ontic w := by
  apply Classical.byContradiction
  intro hNone
  obtain ⟨a, ha⟩ := hPopulation
  have hNoParts : NoNecessaryPartsAt M.ontic w a := by
    intro p _hpa hpNecessary
    exact hNone ⟨p, hpNecessary w hReflexive, hpNecessary⟩
  obtain ⟨sum, hSum⟩ := hFusion ⟨a, ha, hNoParts⟩
  exact hNone (necessaryBeing M.ontic w sum hSum hReflexive hCausal hActual hNonoverlap)

end TruthCore.Results.Causality.ReflexiveActualFusionNecessaryBeing
