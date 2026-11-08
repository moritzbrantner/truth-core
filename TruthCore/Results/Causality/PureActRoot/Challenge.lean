import TruthCore.Causality.PureActRoot

namespace TruthCore.Results.Causality.PureActRoot
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.NecessaryRootUniqueness
open TruthCore.Causality.PureIndiscernibility
open TruthCore.Causality.PureActRoot
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- The whole-roster route supplies an actual necessary root; unrestricted
perfection, strict pure actuality and real thisness at the actual roots make it
the only one. Conditional on seven OPEN premises; no maximum, grades, genus,
has-being or necessity-cause premise is used. -/
theorem uniqueRootFromRealThisness {W B D : Type} (m : Profile W B) (w : W)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hEvery : ActualRootHasEveryPureDetermination m w Has Pure)
    (hPure : ActualRootDeterminationsArePure m w Has Pure)
    (hThis : ActualRootHasRealThisness m w Has) :
    UniqueNecessaryActualRootAt m w := by
  sorry

/-- The same route with the narrower bridge in place of real thisness.
Conditional on seven OPEN premises. -/
theorem uniqueRootFromPureIndiscernibility {W B D : Type} (m : Profile W B) (w : W)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hEvery : ActualRootHasEveryPureDetermination m w Has Pure)
    (hPure : ActualRootDeterminationsArePure m w Has Pure)
    (hBridge : PurelyDeterminedIndiscerniblesIdentical Has Pure) :
    UniqueNecessaryActualRootAt m w := by
  sorry

theorem controls : TruthCore.Causality.PureActRoot.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.PureActRoot
