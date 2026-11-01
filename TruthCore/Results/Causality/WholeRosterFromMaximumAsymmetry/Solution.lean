import TruthCore.Causality.DirectEsseRootUniquenessAtBeing
namespace TruthCore.Results.Causality.WholeRosterFromMaximumAsymmetry
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
/-- The maximum is selected before actualization and remains the SAME source.
No modal necessity or contingent-dependence premise is used here. -/
theorem actualRootMaximum {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hApproach : GradesToMaximumAtBeing InAct MoreIn esse)
    (hEM : ExcludedMiddle) (hAsym : ActualGroundingAsymmetric m w) :
    ∃ n, TruthCore.Causality.NecessaryRootFork.ActualRoot m w n ∧
      IsMaximumIn InAct MoreIn esse n := by
  obtain ⟨a, hc, he⟩ := hPop
  have hMaximum : ∃ n, IsMaximumIn InAct MoreIn esse n := by
    rcases TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaMaximumInBeing.actualFork
      InAct MoreIn esse hEM with h | hUnbounded
    · exact h
    · obtain ⟨b, hb⟩ := hUnbounded a (hExisting a he)
      exact hApproach ⟨b, a, hb⟩
  obtain ⟨n, hMax⟩ := hMaximum
  have hActual : TruthCore.Causality.NecessaryRootFork.ActualConcrete m w n := by
    rcases hEM (n = a) with hEq | hNe
    · exact hEq.symm ▸ (show TruthCore.Causality.NecessaryRootFork.ActualConcrete m w a from ⟨hc, he⟩)
    · have hGround := hEsse n a hNe ⟨hc, he⟩
        (hGenus n hMax a (fun h => hNe h.symm) (hExisting a he))
      exact ⟨hGround.1, hGround.2.1⟩
  refine ⟨n, ⟨hActual, ?_⟩, hMax⟩
  intro y hy
  have hY : TruthCore.Causality.NecessaryRootFork.ActualConcrete m w y := ⟨hy.1, hy.2.1⟩
  rcases hEM (y = n) with hEq | hNe
  · subst y
    exact hAsym n n hActual hActual hy.2.2 hy.2.2
  · have hForward := hEsse n y (fun h => hNe h.symm) hY
      (hGenus n hMax y hNe (hExisting y hy.2.1))
    exact hAsym n y hActual hY hForward.2.2 hy.2.2

theorem wholeRoster {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hApproach : GradesToMaximumAtBeing InAct MoreIn esse)
    (hEM : ExcludedMiddle) (hAsym : ActualGroundingAsymmetric m w) :
    WholeRosterNotTrapped m w := by
  obtain ⟨n, hr, _⟩ := actualRootMaximum m w InAct MoreIn CausesIn esse
    hPop hExisting hEsse hGenus hApproach hEM hAsym
  intro _ hTrap
  have hSource : (TruthCore.Causality.ConcreteExistentialSupply.graph m w).Source ⟨n, hr.1⟩ := by
    rintro ⟨y, hy⟩
    exact hr.2 y.val ⟨y.property.1, y.property.2, hy⟩
  exact hTrap.1 ⟨n, hr.1⟩ trivial hSource
end TruthCore.Results.Causality.WholeRosterFromMaximumAsymmetry
