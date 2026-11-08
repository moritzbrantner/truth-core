module
public import TruthCore.Results.Causality.UniqueRootPerfection.Solution
public import TruthCore.Causality.UniqueRootQuartaControl
@[expose] public section
namespace TruthCore.Results.Causality.UniqueRootQuarta
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.DirectEsseRootPerfectionGoodness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.UniqueRootQuartaControl
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessaryRootUniqueness
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.DirectEsseRootPerfectionGoodness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)


/-- Structural connection, not independent premise defense or God naming.
The causal policy is restricted to esse; no order or world transport occurs. -/
theorem derive {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hRoot : NecessaryPerfectRootAt m w InAct MoreIn esse)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse) :
    MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse := by
  obtain ⟨n, _, _, _, hMax, _⟩ := hRoot
  exact ⟨n, hMax, hGenus n hMax⟩
theorem fromUniqueRoot {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hRoot : UniqueNecessaryActualRootAt m w)
    (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hApproach : GradesToMaximumAtBeing InAct MoreIn esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse) :
    MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse := by
  exact derive m w InAct MoreIn CausesIn esse
    (TruthCore.Results.Causality.UniqueRootPerfection.derive m w InAct MoreIn CausesIn esse
      hRoot hEM hGenus hExisting hEsse hApproach hBeing hPreexist) hGenus

theorem controls : TruthCore.Causality.UniqueRootQuartaControl.Certificate := by
  constructor
  · refine ⟨TruthCore.Causality.UniqueRootQuartaControl.packageHolds, ?_, ?_, ?_⟩
    · intro n hn x hne hx; exact hne.symm
    · exact ⟨false, ⟨trivial, fun _ h => h⟩, fun x hne hx => hne.symm⟩
    · intro h; cases h
  · constructor
    · refine ⟨TruthCore.Causality.UniqueRootQuartaControl.packageHolds, ?_⟩
      intro h
      obtain ⟨n, hn, hc⟩ := h
      cases n
      · exact hc true (by decide) trivial
      · exact hc false (by decide) trivial
    · constructor
      · intro n hn; exact False.elim hn.1
      · intro h; exact h.elim (fun n hn => hn.1.1)
end TruthCore.Results.Causality.UniqueRootQuarta
