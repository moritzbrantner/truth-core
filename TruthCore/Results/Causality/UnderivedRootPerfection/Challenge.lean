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
  sorry
end TruthCore.Results.Causality.UnderivedRootPerfection
