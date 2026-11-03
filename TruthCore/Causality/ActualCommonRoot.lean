import TruthCore.Causality.NecessaryRootFork

/-! Direct coverage of one selected world's actual concreta by a common root.
No necessity, global well-foundedness or explanatory completeness is included. -/
namespace TruthCore.Causality.ActualCommonRoot
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryRootFork (ActualRoot ActualConcrete)

/-- Some actual root n directly grounds every OTHER actual concretum in this
same selected relation and world. The root itself is covered by identity. -/
def ActualCommonRootAt {W B : Type} (m : Profile W B) (w : W) : Prop :=
  ∃ n, ActualRoot m w n ∧
    ∀ x, ActualConcrete m w x → x = n ∨ ActualConcreteGround m w n x

end TruthCore.Causality.ActualCommonRoot
