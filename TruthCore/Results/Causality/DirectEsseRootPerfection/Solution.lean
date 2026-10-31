import TruthCore.Causality.DirectEsseRootPerfectionGoodness
import TruthCore.Results.Causality.DirectEsseRootUniquenessAtBeing.Solution
namespace TruthCore.Results.Causality.DirectEsseRootPerfection
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.NecessaryRootUniqueness
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.DirectEsseRootPerfectionGoodness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic
open TruthCore.Logic.CogitoConcrete
theorem derive {W B Respect : Type} (m : Profile W B) (w : W)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hApproach : GradesToMaximumAtBeing InAct MoreIn esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse) :
    NecessaryPerfectRootAt m w InAct MoreIn esse := by
  obtain ⟨n, hr, hn, hu⟩ :=
    TruthCore.Results.Causality.DirectEsseRootUniquenessAtBeing.uniqueRoot
      m w InAct MoreIn CausesIn esse hPop hWhole hDep hEM hGenus hExisting hEsse hApproach
  obtain ⟨y, hy⟩ := TruthCore.Causality.DirectEsseRootRoute.maximumExistsOfExistingRoot
    m w (fun x (_ : Unit) => InAct x esse) (fun (_ : Unit) y x => MoreIn esse y x)
    () n hr hExisting (fun _ => hApproach) hEM
  have heq := TruthCore.Causality.DirectEsseRootRoute.maximumEqualsRoot
    m w (fun x (_ : Unit) => InAct x esse) (fun (_ : Unit) y x => MoreIn esse y x)
    (fun c x (_ : Unit) => CausesIn c x esse) () n hr hEM (fun _ => hGenus)
    hExisting hEsse y hy
  subst y
  exact ⟨n, hr, hn, hu, hy, perfectOfMaximum InAct MoreIn CausesIn esse n
    hy hGenus hBeing hPreexist hEM⟩
end TruthCore.Results.Causality.DirectEsseRootPerfection
