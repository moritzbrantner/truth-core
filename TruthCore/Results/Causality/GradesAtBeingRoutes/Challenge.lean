import TruthCore.Causality.DirectEsseRootUniquenessAtBeing
import TruthCore.Results.Causality.DirectEsseRootGodExistence.Solution
import TruthCore.Results.Causality.DirectEsseRootGodExistence.ExistenceOnly.Solution

/-! Weak-version siblings of cogito/roster GodExists routes.

The existing routes `DirectEsseRootGodExistence` and
`DirectEsseRootGodExistence.ExistenceOnly` take grades-to-a-maximum in every
respect (`GradesByApproachToAMaximumReading`) but apply it only at the selected
esse respect, inside `actualCore`. The siblings below take the fixed-esse instance
`GradesToMaximumAtBeing` instead and otherwise reuse the existing proofs. The
existing maximum lemmas are instantiated at a one-point respect type whose only
respect is esse: there the all-respects principle is definitionally the esse
instance, and every esse-indexed proposition is unchanged. No other premise is
changed or added; no premise is discharged. -/

namespace TruthCore.Results.Causality.GradesAtBeingRoutes

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.DirectEsseRootRoute
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing (GradesToMaximumAtBeing)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

/-- Strength order: grades-to-a-maximum in every respect gives its instance at
the one respect esse, for the same `InAct` and `MoreIn`. Reuses `restrictGrades`. -/
theorem gradesAtBeingOfGrades {B R : Type} (InAct : B → R → Prop)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn) :
    GradesToMaximumAtBeing InAct MoreIn esse := by
  sorry

/-- Sibling of `DirectEsseRootGodExistence.godExists` with grades at esse: the same
necessary actual first root, named through direct esse correspondence. -/
theorem directEsseRootGodExistsAtBeing {W B Respect : Type} (m : Profile W B) (w : W)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (PriorSimply ComponentOf : B → B → Prop) (IsGod : B → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hApproach : GradesToMaximumAtBeing InAct MoreIn esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) :
    GodExists IsGod := by
  sorry

/-- Sibling of `DirectEsseRootGodExistence.ExistenceOnly.godExists` with grades at
esse: an actual root without contingent dependence, firstness from the priority
correspondence, and direct esse naming. No modal necessity is used or concluded. -/
theorem existenceOnlyGodExistsAtBeing {W B Respect : Type} (m : Profile W B) (w : W)
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
    (hApproach : GradesToMaximumAtBeing InAct MoreIn esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) :
    GodExists IsGod := by
  sorry

end TruthCore.Results.Causality.GradesAtBeingRoutes
