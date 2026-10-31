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

end TruthCore.Results.Causality.ConcreteExistentialSupply
