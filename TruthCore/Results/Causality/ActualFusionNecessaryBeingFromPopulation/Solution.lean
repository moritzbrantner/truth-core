import TruthCore.Results.Causality.ActualFusionNecessaryBeing.Solution
import TruthCore.Explanation.WellFoundedSource

namespace TruthCore.Results.Causality.ActualFusionNecessaryBeingFromPopulation
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Explanation.ExistencePSR
open TruthCore.Explanation.WellFoundedSource (PopulatedAt)
open TruthCore.Causality.ActualFusionNecessaryBeing
open TruthCore.Mereology.FusionNoNecessaryParts

/-- Existing actual population plus conditional selected-family fusion and
four part/causal policies yield bare NE. The Model's explains field is unused;
no PSR, quality, actual wholly-contingent population or sum is presupposed. -/
theorem necessaryBeing {W B : Type} [PartialOrder B] (M : Model W B) (w : W)
    (hPopulation : PopulatedAt M w)
    (hFusion : ConditionalActualFusionAt M.ontic w)
    (hParts : ActualPartsExistAt M.ontic w)
    (hCausal : ActualNoNecessaryPartsHaveCausesAt M.ontic w)
    (hActual : CausesHaveActualEndpointsAt M.ontic w)
    (hNonoverlap : CauseEffectNonoverlapAt M.ontic w) :
    NecessaryBeing M.ontic w := by
  apply Classical.byContradiction
  intro hNone
  obtain ⟨a, ha⟩ := hPopulation
  have hNoParts : NoNecessaryPartsAt M.ontic w a := by
    intro p hpa hpNecessary
    exact hNone ⟨p, hParts a p ha hpa, hpNecessary⟩
  obtain ⟨sum, hSum⟩ := hFusion ⟨a, ha, hNoParts⟩
  exact hNone (TruthCore.Results.Causality.ActualFusionNecessaryBeing.necessaryBeing
    M.ontic w sum hSum hParts hCausal hActual hNonoverlap)

end TruthCore.Results.Causality.ActualFusionNecessaryBeingFromPopulation
