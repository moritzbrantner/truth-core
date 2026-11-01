import TruthCore.Causality.ActualCoverNecessaryBeing

namespace TruthCore.Results.Causality.ActualCoverNecessaryBeing
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.ActualFusionNecessaryBeing
open TruthCore.Causality.ActualCoverNecessaryBeing
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Explanation.ExistencePSR
open TruthCore.Explanation.WellFoundedSource (PopulatedAt)
open TruthCore.Mereology.FusionNoNecessaryParts

/-- SAME candidate/family/world: keep the actual guard and project Fusion.upper.
The no-extra-parts clause is not needed; no converse is asserted. -/
theorem actualCoverOfFusion {W B : Type} [PartialOrder B] (m : Ontic W B) (w : W)
    (sum : B) (hFusion : ActualFusionAt m w sum) : ActualCoverAt m w sum :=
  ⟨hFusion.1, hFusion.2.1⟩

/-- Preserve the SAME nonempty family and selected actual sum. -/
theorem conditionalCoverOfFusion {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) (hFusion : ConditionalActualFusionAt m w) :
    ConditionalActualCoverAt m w := by
  intro hNonempty
  obtain ⟨sum, hs⟩ := hFusion hNonempty
  exact ⟨sum, actualCoverOfFusion m w sum hs⟩

/-- SAME primitive causal relation and order: a cause which is part of its
effect would itself be a common-part witness contradicting nonoverlap. -/
theorem nonpartOfNonoverlap {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) (hNonoverlap : CauseEffectNonoverlapAt m w) :
    CauseNotPartOfEffectAt m w := by
  intro c e hCause hPart
  exact hNonoverlap c e hCause ⟨c, le_refl c, hPart⟩

/-- Unregistered selected-cover tail: no fusion or full nonoverlap is needed.
The endpoint is SOME actual NE, not necessity of the selected causal witness. -/
theorem necessaryBeingOfCover {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) (cover : B) (hCover : ActualCoverAt m w cover)
    (hReflexive : ActualReflexive m w)
    (hCausal : ActualNoNecessaryPartsHaveCausesAt m w)
    (hActual : CausesHaveActualEndpointsAt m w)
    (hNonpart : CauseNotPartOfEffectAt m w) : NecessaryBeing m w := by
  apply Classical.byContradiction
  intro hNone
  have hNoParts : ∀ x, NoNecessaryPartsAt m w x := by
    intro x p _hpx hpNecessary
    exact hNone ⟨p, hpNecessary w hReflexive, hpNecessary⟩
  obtain ⟨c, hCause⟩ := hCausal cover hCover.1 (hNoParts cover)
  have hcActual : m.ExistsAt w c := (hActual c cover hCause).1
  exact hNonpart c cover hCause (hCover.2 c ⟨hcActual, hNoParts c⟩)

/-- Six explicit inputs derive SOME bare actual necessary individual. Actual
coverage and cause-nonparthood replace fusion and full causal nonoverlap. -/
theorem fromPopulation {W B : Type} [PartialOrder B] (M : Model W B) (w : W)
    (hPopulation : PopulatedAt M w)
    (hCover : ConditionalActualCoverAt M.ontic w)
    (hReflexive : ActualReflexive M.ontic w)
    (hCausal : ActualNoNecessaryPartsHaveCausesAt M.ontic w)
    (hActual : CausesHaveActualEndpointsAt M.ontic w)
    (hNonpart : CauseNotPartOfEffectAt M.ontic w) : NecessaryBeing M.ontic w := by
  apply Classical.byContradiction
  intro hNone
  obtain ⟨a, ha⟩ := hPopulation
  have haNoParts : NoNecessaryPartsAt M.ontic w a := by
    intro p _hpa hpNecessary
    exact hNone ⟨p, hpNecessary w hReflexive, hpNecessary⟩
  obtain ⟨cover, hActualCover⟩ := hCover ⟨a, ha, haNoParts⟩
  exact hNone (necessaryBeingOfCover M.ontic w cover hActualCover
    hReflexive hCausal hActual hNonpart)

end TruthCore.Results.Causality.ActualCoverNecessaryBeing
