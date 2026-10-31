import TruthCore.Causality.RootWithoutLimitingPrinciple
import TruthCore.Case.Catholicism.StageTwo
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.IntellectWill
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article8

/-! Same-witness conditional attribute composition. Intellect and will retain
existing primitive predicates constrained by the q14/q19 readings; no omniscience,
free choice, divine naming or source applicability is established. -/
namespace TruthCore.Causality.RootIntellectWill
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (IsSimple RemoteFromAll)

/-- ONE actual concrete necessary root retains represented essence/esse identity,
firstness, noncomposition, matter-form exclusion, remoteness, intellect and will.
Noncomposition concerns what composes n; remoteness concerns n entering others.
Neither uniqueness, God nor complete explanatory adequacy is asserted. -/
def NecessaryRootIntellectWillAt {W B P R : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop)
    (Composite MatterForm HasIntellect HasWill : B → Prop) : Prop :=
  ∃ n, ActualRoot m w n ∧ NecessaryAt m.ontic w n ∧
    p.esseOf n = p.essenceOf n ∧ IsSimple Composite n ∧ IsFirstBeing PriorSimply n ∧
    ¬ MatterForm n ∧ RemoteFromAll ComponentOf n ∧ HasIntellect n ∧ HasWill n

end TruthCore.Causality.RootIntellectWill
