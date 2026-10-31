import TruthCore.Causality.NecessaryConcreteRouteBridge
import TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaMaximumInBeing.Solution

namespace TruthCore.Causality.NecessaryRootUniqueness
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (NecessaryBeingHasBeing)
open TruthCore.Logic (ExcludedMiddle)

/-- Source-free, non-corpus helper. A supplied necessary individual provides
esse population through the explicit has-being bridge. The existing actual
fork and its unbounded-horn contradiction produce a maximum. No grounding root,
grades at truth, efficient-cause comparison or God identification is assumed. -/
theorem maximumExistsOfNecessaryAt {W B Respect : Type} (m : Profile W B) (w : W)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop) (esse : Respect)
    (n : B) (hn : NecessaryAt m.ontic w n)
    (hHasBeing : NecessaryBeingHasBeing (modalPossible m w) (modalIsAt m) InAct esse)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hEM : ExcludedMiddle) : ∃ x, IsMaximumIn InAct MoreIn esse x := by
  have hActual : ∃ x, InAct x esse :=
    ⟨n, hHasBeing n (isNecessaryOfNecessaryAt m w n hn)⟩
  rcases TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaMaximumInBeing.actualFork
    InAct MoreIn esse hEM with hMaximum | hUnbounded
  · exact hMaximum
  · exact (TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaMaximumInBeing.actualCore
      InAct MoreIn esse hApproach hActual hUnbounded).elim

/-- Exactly one actual concrete root of the selected relation at w exists, and
this same individual is necessary at accessible worlds. This excludes no
necessary nonroots and asserts no cross-world rootness, unique efficient cause,
universal ancestry, or divine identity. -/
def UniqueNecessaryActualRootAt {W B : Type} (m : Profile W B) (w : W) : Prop :=
  ∃ n, ActualRoot m w n ∧ NecessaryAt m.ontic w n ∧
    ∀ x, ActualRoot m w x → x = n

end TruthCore.Causality.NecessaryRootUniqueness
