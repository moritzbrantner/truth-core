import TruthCore.Causality.RootIntellectWill

/-! Same-witness joint endpoint only: no-potency is conjoined INSIDE the existing
existential root tuple. No separate existential witnesses are identified.
No source reading, positive perfection, God, eternity or reality truth is added. -/
namespace TruthCore.Causality.RootIntellectWillPureAct
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (IsSimple RemoteFromAll)

/-- The exact old root/intellect/will witness conjunction together with no
potency in any supplied respect, for ONE and the SAME n. The same q3 profile
supplies the act dictionary to act-priority/exclusivity; completeness of its
respect domain and metaphysical applicability remain open. -/
def NecessaryRootIntellectWillPureActAt {W B P R : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop)
    (Composite MatterForm HasIntellect HasWill : B → Prop)
    (InPotency : B → R → Prop) : Prop :=
  ∃ n, ActualRoot m w n ∧ NecessaryAt m.ontic w n ∧
    p.esseOf n = p.essenceOf n ∧ IsSimple Composite n ∧ IsFirstBeing PriorSimply n ∧
    ¬ MatterForm n ∧ RemoteFromAll ComponentOf n ∧ HasIntellect n ∧ HasWill n ∧ PureAct InPotency n

end TruthCore.Causality.RootIntellectWillPureAct
