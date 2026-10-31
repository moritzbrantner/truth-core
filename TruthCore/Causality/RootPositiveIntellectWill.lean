import TruthCore.Causality.DirectEsseRootPerfectionGoodness
import TruthCore.Causality.RootIntellectWill
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Cause

/-! Same selected root, positive and structural attributes. This packages
conditional consequences without a God name, all-necessary-individual uniqueness,
moral perfection, cognitive adequacy or a full-nine-attribute claim. -/
namespace TruthCore.Causality.RootPositiveIntellectWill
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.DirectEsseRootPerfectionGoodness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

/-- ONE witness retains the existing perfect-root body and causal supreme
goodness, represented esse/essence identity, noncomposition, firstness,
matter/form exclusion, remoteness, intellect and will. Dictionary applicability
and formal-or-eminent/cognitive/causal interpretation remain OPEN. -/
def NecessaryPositiveRootIntellectWillAt {W B P R : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B P R) (GoodIn : B → R → Prop)
    (MoreIn : R → B → B → Prop)
    (PriorSimply ComponentOf : B → B → Prop)
    (Composite MatterForm HasIntellect HasWill : B → Prop) : Prop :=
  ∃ n, PerfectRootAt m w p.InAct MoreIn p.esse n ∧
    IsSupremelyGood p.InAct GoodIn p.CausesIn p.esse n ∧
    p.esseOf n = p.essenceOf n ∧ IsSimple Composite n ∧
    IsFirstBeing PriorSimply n ∧ ¬ MatterForm n ∧ RemoteFromAll ComponentOf n ∧
    HasIntellect n ∧ HasWill n
end TruthCore.Causality.RootPositiveIntellectWill
