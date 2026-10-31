import TruthCore.Causality.ConcreteExistentialSupply

/-! A whole-roster foundation condition, source-free and relative to the selected
actual-concrete grounding relation. Unlike Escape, it tests only Set.univ.
Its applicability to real existential explanation remains an open premise. -/
namespace TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.ConcreteExistentialSupply
open TruthCore.Causality.JointGroups
open TruthCore.Causality.DerivativeJointPower

/-- If the whole actual concrete roster is inhabited, that roster is not a Trap,
with intrinsic contributions interpreted as sources of this selected relation.
No condition is imposed on proper subsets, chain lengths or all-branch WF.
This interpretation is not automatically the owner's verbal explanatory norm. -/
def WholeRosterNotTrapped {W B : Type} (m : Profile W B) (w : W) : Prop :=
  (Set.univ : Set {b // ActualConcrete m w b}).Nonempty →
    ¬ Trap (recorded (graph m w)) (graph m w).Source Set.univ

end TruthCore.Causality.WholeRosterFoundation
