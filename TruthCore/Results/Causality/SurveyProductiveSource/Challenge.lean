import TruthCore.Causality.SurveyProductiveSource
import TruthCore.Results.Causality.PossibleCausalSourceNecessity.Solution

namespace TruthCore.Results.Causality.SurveyProductiveSource
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.SurveyProductiveSource
open TruthCore.Causality.PossibleCausalSourceNecessity
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Modal (Euclidean)

/-- Reuse the ordinary sameSource consequence, then classify its SAME c from
its outgoing production at v. Necessity and existence are retained at w;
sourcehood and production are asserted only at v. All seven inputs remain open.
No ontic/own-nature necessity or source capability interpretation follows. -/
theorem necessaryConcrete {W B : Type} (p : Profile W B) (w : W)
    (em : ExcludedMiddle) (causal : LocalCausalPrinciple p.ontic)
    (euclidean : Euclidean p.ontic.frame) (reflexive : ActualReflexive p.ontic w)
    (opportunity : PossiblyFailedHeadlessCoverage p.ontic w)
    (productive : ProductiveSources p.ontic w)
    (calibration : AccessibleCausersConcrete p.ontic p.concrete w) :
    NecessaryConcreteAt p w := by
  sorry

/-- Omitting productivity permits an isolated source; omitting calibration
permits a productive nonconcrete source. Both clauses hold with a concrete
productive source. Finite relative satisfiability, not independent warrant. -/
theorem controls : Controls := by
  sorry

end TruthCore.Results.Causality.SurveyProductiveSource
