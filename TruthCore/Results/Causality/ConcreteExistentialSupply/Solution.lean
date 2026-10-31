import TruthCore.Causality.ConcreteExistentialSupply
import TruthCore.Results.Causality.DerivativeJointPower.Solution
import TruthCore.Results.Causality.NecessaryRootFork.Solution
import TruthCore.Results.Causality.NecessaryConcreteUnderived.Solution

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
  obtain ⟨target, hTarget⟩ := hSupply
  obtain ⟨source, _, hSource⟩ :=
    TruthCore.Results.Causality.DerivativeJointPower.source_path
      (TruthCore.Causality.JointGroups.recorded (graph m w)) (graph m w).Source
      (fun g _ => g.property) target hTarget
  have hRoot : ActualRoot m w source.val := by
    refine ⟨source.property, ?_⟩
    intro candidate hGround
    exact hSource ⟨⟨candidate, hGround.1, hGround.2.1⟩, hGround.2.2⟩
  cases hEM (TruthCore.German.Kant.CosmologicalInference.NecessaryAt m.ontic w source.val) with
  | inl hNecessary => exact ⟨source.val, source.property.1, source.property.2, hNecessary⟩
  | inr hNotNecessary =>
    exact False.elim
      ((everyContingentGrounded_iff_noContingentRoot m w hEM).mp hDep
        (contingentRootOfNonnecessary m w hEM ⟨source.val, hRoot, hNotNecessary⟩))

/-- Existing joint model retains an actual contingent concrete effect. -/
theorem jointWitness : TruthCore.Causality.ConcreteExistentialSupply.JointWitness := by
  let m := TruthCore.Causality.NecessaryConcreteUnderived.witnessProfile
  have old := TruthCore.Results.Causality.NecessaryConcreteUnderived.jointWitness
  refine ⟨?_, old.2.2.1, old.2.2.2.2.2.2⟩
  refine ⟨⟨false, trivial, Or.inl rfl⟩, ?_⟩
  apply TruthCore.Causality.DerivativeJointPower.Supply.intrinsic
  rintro ⟨candidate, hEdge⟩
  exact Bool.noConfusion hEdge.2.1

end TruthCore.Results.Causality.ConcreteExistentialSupply
