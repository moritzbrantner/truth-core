import TruthCore.Causality.NecessaryConcreteRouteBridge
import TruthCore.Causality.ExistenceActuality
import TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaMaximumInBeing.Solution

/-! Source-free non-corpus helpers for the existing direct esse-to-selected-ground
interface. They assert no independent warrant for that interface or completeness
of the resulting causal explanation. -/
namespace TruthCore.Causality.DirectEsseRootRoute
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)

/-- Every supplied maximum is the supplied actual root. Unlike the necessity-
cause route, the direct correspondence applies to actual concrete targets. -/
theorem maximumEqualsRoot {W B Respect : Type} (m : Profile W B) (w : W)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect) (n : B)
    (hr : ActualRoot m w n) (hEM : ExcludedMiddle)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse) :
    ∀ y, IsMaximumIn InAct MoreIn esse y → y = n := by
  intro y hy
  rcases hEM (y = n) with h | h
  · exact h
  · exact (hr.2 y (hEsse y n h hr.1
      (hGenus esse y hy n (fun hEq => h hEq.symm) (hExisting n hr.1.2)))).elim

/-- An existing root supplies esse population through the explicit existence-
actuality interface. No modal necessary-being interface is used. -/
theorem maximumExistsOfExistingRoot {W B Respect : Type} (m : Profile W B) (w : W)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop) (esse : Respect)
    (n : B) (hr : ActualRoot m w n)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hEM : ExcludedMiddle) : ∃ y, IsMaximumIn InAct MoreIn esse y := by
  rcases TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaMaximumInBeing.actualFork
    InAct MoreIn esse hEM with h | h
  · exact h
  · exact (TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaMaximumInBeing.actualCore
      InAct MoreIn esse hApproach ⟨n, hExisting n hr.1.2⟩ h).elim

/-- Preserve the supplied necessary actual root and derive direct selected-ground
coverage of every other actual concretum, including contingent ones. Coverage
does not assert independent adequacy or complete explanatory sufficiency. -/
theorem necessaryRootCommonGround {W B Respect : Type} (m : Profile W B) (w : W)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect) (n : B)
    (hr : ActualRoot m w n) (hn : NecessaryAt m.ontic w n) (hEM : ExcludedMiddle)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn) :
    ActualRoot m w n ∧ NecessaryAt m.ontic w n ∧
      ∀ x, ActualConcrete m w x → x ≠ n → ActualConcreteGround m w n x := by
  obtain ⟨y, hy⟩ := maximumExistsOfExistingRoot m w InAct MoreIn esse n hr hExisting hApproach hEM
  have heq := maximumEqualsRoot m w InAct MoreIn CausesIn esse n hr hEM hGenus hExisting hEsse y hy
  subst y
  refine ⟨hr, hn, ?_⟩
  intro x hx hne
  exact hEsse n x (fun hEq => hne hEq.symm) hx (hGenus esse n hy x hne (hExisting x hx.2))

end TruthCore.Causality.DirectEsseRootRoute
