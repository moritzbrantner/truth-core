import TruthCore.Causality.NecessaryConcreteUnderived
import TruthCore.Causality.DirectEsseRootPerfectionGoodness
import TruthCore.Logic.ExcludedMiddle

namespace TruthCore.Results.Causality.UnderivedRootPerfection
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.DirectEsseRootPerfectionGoodness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)

/-- Retain the supplied underived witness as the selected unique necessary
actual root and perfect esse maximum. Only its support exclusion at w is used;
no all-world attributes or uniqueness of all necessary individuals follows. -/
theorem derive {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hUnderived : NecessaryConcreteUnderivedAt m w)
    (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hApproach : GradesToMaximumAtBeing InAct MoreIn esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse) :
    NecessaryPerfectRootAt m w InAct MoreIn esse := by
  obtain ⟨n, hc, he, hn, hu⟩ := hUnderived
  have hr : ActualRoot m w n := by
    refine ⟨⟨hc, he⟩, ?_⟩
    intro c hGround
    exact hu w c hGround.1 hGround.2.1 hGround.2.2
  let act : B → Unit → Prop := fun x _ => InAct x esse
  let more : Unit → B → B → Prop := fun _ y x => MoreIn esse y x
  let cause : B → B → Unit → Prop := fun c x _ => CausesIn c x esse
  obtain ⟨maximum, hMaximum⟩ :=
    TruthCore.Causality.DirectEsseRootRoute.maximumExistsOfExistingRoot
      m w act more () n hr hExisting (fun _ => hApproach) hEM
  have hMaximumN := TruthCore.Causality.DirectEsseRootRoute.maximumEqualsRoot
    m w act more cause () n hr hEM (fun _ => hGenus) hExisting hEsse maximum hMaximum
  have hUnique : ∀ x, ActualRoot m w x → x = n := by
    intro x hx
    have hMaximumX := TruthCore.Causality.DirectEsseRootRoute.maximumEqualsRoot
      m w act more cause () x hx hEM (fun _ => hGenus) hExisting hEsse maximum hMaximum
    exact hMaximumX.symm.trans hMaximumN
  have hMax : IsMaximumIn InAct MoreIn esse n := hMaximumN ▸ hMaximum
  exact ⟨n, hr, hn, hUnique, hMax,
    perfectOfMaximum InAct MoreIn CausesIn esse n hMax hGenus hBeing hPreexist hEM⟩
end TruthCore.Results.Causality.UnderivedRootPerfection
