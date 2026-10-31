import TruthCore.Causality.NecessaryConcreteRouteBridge

/-! Existential endpoints for the same selected actual necessary root. These
definitions do not identify firstness with uniqueness or maximality. Applicability
of the selected grounding relation and the simply-prior bridge remains open. -/
namespace TruthCore.Causality.NecessaryFirstBeing

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae (IsFirstBeing PureAct)

/-- An actual concrete root is necessary at accessible worlds and has no distinct
simply-prior predecessor. Rootness is only at the selected world and relation;
neither uniqueness nor a maximum or God is asserted. -/
def NecessaryActualFirstAt {W B : Type} (m : Profile W B) (w : W)
    (PriorSimply : B → B → Prop) : Prop :=
  ∃ n, ActualRoot m w n ∧ NecessaryAt m.ontic w n ∧ IsFirstBeing PriorSimply n

/-- The very same root, necessary individual and first being has no potency in
any supplied respect. This states no positive actuality or completeness of the
respect domain, and no uniqueness, divine naming or universal causal coverage. -/
def NecessaryActualFirstPureActAt {W B Respect : Type} (m : Profile W B) (w : W)
    (PriorSimply : B → B → Prop) (InPotency : B → Respect → Prop) : Prop :=
  ∃ n, ActualRoot m w n ∧ NecessaryAt m.ontic w n ∧
    IsFirstBeing PriorSimply n ∧ PureAct InPotency n

end TruthCore.Causality.NecessaryFirstBeing
