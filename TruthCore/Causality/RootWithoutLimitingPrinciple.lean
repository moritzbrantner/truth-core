import TruthCore.Causality.RootEssenceIdentity
import TruthCore.Causality.RootMultiplication

/-! Source-free composition endpoint. Absence of the existing three represented
limitation horns is not Q7 unreceivedness or infinity, common nature or uniqueness. -/
namespace TruthCore.Causality.RootWithoutLimitingPrinciple
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.RootMultiplication (HasLimitingPrinciple)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)

/-- The same actual concrete root is necessary at worlds accessible from `w`
and has none of the three supplied limitation horns. The essence/esse maps are
exactly those of the supplied q3 profile. Rootness remains world-relative;
this does not assert first-mover status or metaphysical unlimitedness. -/
def NecessaryRootWithoutLimitingPrincipleAt {W B P R : Type}
    (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (Composite : B → Prop) (PriorSimply : B → B → Prop) : Prop :=
  ∃ n, ActualRoot m w n ∧ NecessaryAt m.ontic w n ∧
    ¬ HasLimitingPrinciple Composite PriorSimply p.essenceOf p.esseOf n

end TruthCore.Causality.RootWithoutLimitingPrinciple
