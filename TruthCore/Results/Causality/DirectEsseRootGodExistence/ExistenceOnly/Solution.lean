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

/-- Preserve the same actual first root through direct esse naming without
contingent-dependence or modal-necessity premises. This helper asserts no
NecessaryAt property of that individual. -/
theorem sameWitnessGod {W B Respect : Type} (m : Profile W B) (w : W)
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
    ∃ n, ActualRoot m w n ∧ IsFirstBeing PriorSimply n ∧ IsGod n := by
  obtain ⟨n, hr⟩ := TruthCore.Results.Causality.WholeRosterFoundation.actualRootExists
    m w hPop hWhole hEM
  have hFirst : IsFirstBeing PriorSimply n := by
    intro y hy
    rcases hEM (y = n) with hEq | hNe
    · exact hEq
    · exact (hr.2 y (hPrior y n hNe hy)).elim
  have hGod := TruthCore.Results.Causality.DirectEsseRootGodExistence.godOfRoot
    m w InAct MoreIn CausesIn esse PriorSimply ComponentOf IsGod n hr hFirst hEM
    hGenus hExisting hEsse hApproach hBeing hTransfer hNoComponent hFull
  exact ⟨n, hr, hFirst, hGod⟩

/-- Project existing GodExists from the twelve retained inputs. The same
actual first root is named, but modal necessity is not part of this conclusion
or of the witness-preserving helper. All semantic and nominal bridges remain open. -/
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
  obtain ⟨n, _, _, hGod⟩ := sameWitnessGod m w InAct MoreIn CausesIn esse
    PriorSimply ComponentOf IsGod hPop hWhole hEM hPrior hGenus hExisting hEsse
    hApproach hBeing hTransfer hNoComponent hFull
  exact ⟨n, hGod⟩

end TruthCore.Results.Causality.DirectEsseRootGodExistence.ExistenceOnly
