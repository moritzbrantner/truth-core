import TruthCore.Causality.NecessaryConcreteUnderived
import TruthCore.Causality.ActualCoverNecessaryBeing
import TruthCore.Results.Causality.ActualCoverNecessaryBeing.Solution

namespace TruthCore.Results.Causality.ConcreteActualCoverNecessaryBeing
open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)
open TruthCore.Causality.NecessaryConcreteUnderived (concreteOntic)
open TruthCore.Causality.ActualFusionNecessaryBeing
open TruthCore.Causality.ActualCoverNecessaryBeing
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- AP-free assembly on the existing concrete carrier. All cover, part and
causal policies concern that SAME restricted ontology. No restriction from
full-carrier policies, production-ground identity or sourcehood is inferred. -/
theorem derive {W B : Type} (m : Profile W B) (w : W)
    [PartialOrder {b // m.concrete b}]
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hCover : ConditionalActualCoverAt (concreteOntic m) w)
    (hRef : ActualReflexive (concreteOntic m) w)
    (hCausal : ActualNoNecessaryPartsHaveCausesAt (concreteOntic m) w)
    (hActual : CausesHaveActualEndpointsAt (concreteOntic m) w)
    (hNonpart : CauseNotPartOfEffectAt (concreteOntic m) w) :
    NecessaryConcreteAt m w := by
  have hNecessary : TruthCore.German.Kant.CosmologicalInference.NecessaryBeing
      (concreteOntic m) w := by
    apply Classical.byContradiction
    intro hNone
    obtain ⟨a, hc, ha⟩ := hPop
    have hNoParts : TruthCore.Mereology.FusionNoNecessaryParts.NoNecessaryPartsAt
        (concreteOntic m) w ⟨a, hc⟩ := by
      intro p _hPart hNecessary
      exact hNone ⟨p, hNecessary w hRef, hNecessary⟩
    obtain ⟨cover, hActualCover⟩ := hCover ⟨⟨a, hc⟩, ha, hNoParts⟩
    exact hNone
      (TruthCore.Results.Causality.ActualCoverNecessaryBeing.necessaryBeingOfCover
        (concreteOntic m) w cover hActualCover hRef hCausal hActual hNonpart)
  obtain ⟨c, hc, hn⟩ := hNecessary
  exact ⟨c.val, c.property, hc, hn⟩

end TruthCore.Results.Causality.ConcreteActualCoverNecessaryBeing
