import TruthCore.Causality.NecessaryRootUniqueness
import TruthCore.Causality.DirectEsseRootPerfectionGoodness
import TruthCore.Logic.ExcludedMiddle

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
  sorry
end TruthCore.Results.Causality.UniqueRootPerfection
