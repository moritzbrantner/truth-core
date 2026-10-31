import TruthCore.Causality.NecessaryFirstBeing
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article8

namespace TruthCore.Causality.NecessaryFirstAttributes
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae (IsFirstBeing PureAct)
open TruthCore.Case.Catholicism (RemoteFromAll)

/-- One and the same actual concrete root is necessary, first, potency-free,
noncomposite, and a component of nothing under the supplied predicates. This
does not exclude other composition notions without their own interfaces, and
asserts neither positive actuality nor numerical uniqueness or divine naming. -/
def NecessaryFirstAttributesAt {W B Respect : Type} (m : Profile W B) (w : W)
    (PriorSimply ComponentOf : B → B → Prop)
    (InPotency : B → Respect → Prop) (Composite : B → Prop) : Prop :=
  ∃ n, ActualRoot m w n ∧ NecessaryAt m.ontic w n ∧
    IsFirstBeing PriorSimply n ∧ PureAct InPotency n ∧
    ¬ Composite n ∧ RemoteFromAll ComponentOf n

end TruthCore.Causality.NecessaryFirstAttributes
