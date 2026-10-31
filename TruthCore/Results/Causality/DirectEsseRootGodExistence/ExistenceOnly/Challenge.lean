import TruthCore.Results.Causality.DirectEsseRootGodExistence.Solution
import TruthCore.Results.Causality.NecessaryFirstBeing.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.Solution

namespace TruthCore.Results.Causality.DirectEsseRootGodExistence.ExistenceOnly

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.DirectEsseRootRoute
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

/-- Twelve-input GodExists composition. Contingent dependence is unnecessary
for naming an actual first root via direct esse correspondence; this theorem
does not assert modal necessity of its named individual. -/
theorem godExists {W B Respect : Type} (m : Profile W B) (w : W)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (PriorSimply ComponentOf : B → B → Prop) (IsGod : B → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hEM : ExcludedMiddle)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) :
    GodExists IsGod := by
  sorry

end TruthCore.Results.Causality.DirectEsseRootGodExistence.ExistenceOnly
