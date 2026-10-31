import TruthCore.Causality.ConcreteExistentialSupply

namespace TruthCore.Results.Causality.ConcreteExistentialSupply
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.ConcreteExistentialSupply
open TruthCore.Logic (ExcludedMiddle)

/-- Cumulative argument: existing joint supply extracts an actual concrete
source; contingent dependence excludes its contingency. The conclusion is
necessary concrete existence, not uniqueness, permanent underivedness or God.
Actual supply already includes actual population; global WF is not assumed. -/
theorem necessaryConcreteOfSupply {W B : Type} (m : Profile W B) (w : W)
    (hSupply : ActualConcreteSupply m w)
    (hDep : EveryContingentGroundedAt m w)
    (hEM : ExcludedMiddle) : NecessaryConcreteAt m w := by
  sorry

/-- Existing joint model retains an actual contingent concrete effect. -/
theorem jointWitness : TruthCore.Causality.ConcreteExistentialSupply.JointWitness := by
  sorry

/-- The supply application's existential strength is exposed exactly. -/
theorem supplyRootEquivalence : SupplyRootEquivalence := by
  sorry

/-- Full cumulative route from actual existence and the existing borrowing-cut
principle, followed by contingent-root exclusion. No necessary witness assumed. -/
theorem necessaryConcreteOfBorrowingEscape {W B : Type} (m : Profile W B) (w : W)
    (hPop : TruthCore.Logic.CogitoConcrete.InhabitedConcreteAt m.ontic m.concrete w)
    (hEscape : ActualConcreteBorrowingEscape m w)
    (hDep : EveryContingentGroundedAt m w)
    (hEM : ExcludedMiddle) : NecessaryConcreteAt m w := by
  sorry

/-- Exact relation of the cut principle to the earlier actual WF premise. -/
theorem borrowingEscapeWFEquivalence : BorrowingEscapeWFEquivalence := by
  sorry

/-- Corpus-facing connection into the existing actual-grounding WF premise. -/
theorem actualWfOfBorrowingEscape {W B : Type} (m : Profile W B) (w : W)
    (hEscape : ActualConcreteBorrowingEscape m w)
    (hEM : ExcludedMiddle) : ActualGroundingWF m w := by
  sorry

end TruthCore.Results.Causality.ConcreteExistentialSupply
