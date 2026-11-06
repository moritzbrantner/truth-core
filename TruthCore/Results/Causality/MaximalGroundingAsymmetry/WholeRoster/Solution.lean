module

public import TruthCore.Causality.MaximalGroundingAsymmetry
public import TruthCore.Results.Causality.WholeRosterRootEquivalence.Solution

@[expose] public section
namespace TruthCore.Results.Causality.MaximalGroundingAsymmetry.WholeRoster
open TruthCore.Causality.MaximalGroundingAsymmetry
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.NecessaryRootUniqueness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic
open TruthCore.Logic.CogitoConcrete

theorem actualRootMaximum {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hApproach : GradesToMaximumAtBeing InAct MoreIn esse)
    (hEM : ExcludedMiddle) (hAsym : AtMaximalTarget m w InAct MoreIn esse) :
    ∃ n, ActualRoot m w n ∧ IsMaximumIn InAct MoreIn esse n := by
  obtain ⟨a, hc, he⟩ := hPop
  have hMaximum : ∃ n, IsMaximumIn InAct MoreIn esse n := by
    rcases TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaMaximumInBeing.actualFork
      InAct MoreIn esse hEM with h | hUnbounded
    · exact h
    · obtain ⟨b, hb⟩ := hUnbounded a (hExisting a he)
      exact hApproach ⟨b, a, hb⟩
  obtain ⟨n, hMax⟩ := hMaximum
  have hActual : ActualConcrete m w n := by
    rcases hEM (n = a) with hEq | hNe
    · exact hEq.symm ▸ (show ActualConcrete m w a from ⟨hc, he⟩)
    · have hGround := hEsse n a hNe ⟨hc, he⟩
        (hGenus n hMax a (fun h => hNe h.symm) (hExisting a he))
      exact ⟨hGround.1, hGround.2.1⟩
  refine ⟨n, ⟨hActual, ?_⟩, hMax⟩
  intro y hy
  have hY : ActualConcrete m w y := ⟨hy.1, hy.2.1⟩
  rcases hEM (y = n) with hEq | hNe
  · subst y
    exact hAsym n n hActual hActual hMax hy.2.2 hy.2.2
  · have hForward := hEsse n y (fun h => hNe h.symm) hY
      (hGenus n hMax y hNe (hExisting y hy.2.1))
    exact hAsym y n hY hActual hMax hy.2.2 hForward.2.2

/-- Analyst same-dictionary scope consequence; all original source/Challenge interfaces preserved. -/
theorem wholeRoster {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hApproach : GradesToMaximumAtBeing InAct MoreIn esse)
    (hEM : ExcludedMiddle) (hAsym : AtMaximalTarget m w InAct MoreIn esse) : WholeRosterNotTrapped m w := by
  obtain ⟨n, hr, _⟩ := actualRootMaximum m w InAct MoreIn CausesIn esse
    hPop hExisting hEsse hGenus hApproach hEM hAsym
  exact TruthCore.Results.Causality.WholeRosterRootEquivalence.wholeRosterOfRoot m w ⟨n, hr⟩

end TruthCore.Results.Causality.MaximalGroundingAsymmetry.WholeRoster
