import TruthCore.Causality.NecessaryConcreteUnderived
import TruthCore.Causality.ActualCoverNecessaryBeing

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
  sorry

end TruthCore.Results.Causality.ConcreteActualCoverNecessaryBeing
