import TruthCore.Results.Causality.DirectEsseRootPerfection.Solution
import TruthCore.Causality.DirectEsseRootPerfectionGoodness
import TruthCore.Results.Causality.DirectEsseRootUniquenessAtBeing.Solution
namespace TruthCore.Results.Causality.DirectEsseRootPerfectionGoodness
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
    (InAct GoodIn : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hApproach : GradesToMaximumAtBeing InAct MoreIn esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse)
    (hGoodness : GoodnessIsActualityReading GoodIn InAct)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse) :
    NecessaryPerfectSupremelyGoodRootAt m w InAct GoodIn MoreIn CausesIn esse := by
  obtain ⟨n, hn⟩ := TruthCore.Results.Causality.DirectEsseRootPerfection.derive
    m w InAct MoreIn CausesIn esse hPop hWhole hDep hEM hGenus hExisting hEsse hApproach
    hBeing hPreexist
  exact ⟨n, hn, supremelyGoodOfMaximum InAct GoodIn MoreIn CausesIn esse n
    hn.2.2.2.1 hGenus hBeing hGoodness hTransfer⟩
end TruthCore.Results.Causality.DirectEsseRootPerfectionGoodness
