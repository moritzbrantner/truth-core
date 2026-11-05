module

public import TruthCore.Causality.NecessaryRootUniqueness
public import TruthCore.Causality.DirectEsseRootPerfectionGoodness
public import TruthCore.Logic.ExcludedMiddle

@[expose] public section

namespace TruthCore.Results.Causality.UniqueRootPerfection
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessaryRootUniqueness
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.DirectEsseRootPerfectionGoodness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)

/-- Preserve the supplied unique necessary actual root while deriving its selected-world esse maximum and perfection. -/
theorem derive {W B R : Type} (m : Profile W B) (w : W)
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
    NecessaryPerfectRootAt m w InAct MoreIn esse := by
  obtain ⟨n, hr, hn, hUnique⟩ := hRoot
  let act : B → Unit → Prop := fun x _ => InAct x esse
  let more : Unit → B → B → Prop := fun _ y x => MoreIn esse y x
  let cause : B → B → Unit → Prop := fun c x _ => CausesIn c x esse
  obtain ⟨maximum, hMaximum⟩ :=
    TruthCore.Causality.DirectEsseRootRoute.maximumExistsOfExistingRoot
      m w act more () n hr hExisting (fun _ => hApproach) hEM
  have hMaximumN := TruthCore.Causality.DirectEsseRootRoute.maximumEqualsRoot
    m w act more cause () n hr hEM (fun _ => hGenus) hExisting hEsse maximum hMaximum
  have hMax : IsMaximumIn InAct MoreIn esse n := hMaximumN ▸ hMaximum
  exact ⟨n, hr, hn, hUnique, hMax,
    perfectOfMaximum InAct MoreIn CausesIn esse n hMax hGenus hBeing hPreexist hEM⟩
end TruthCore.Results.Causality.UniqueRootPerfection
