module

public import TruthCore.Causality.DirectEsseRootUniquenessAtBeing
public import TruthCore.Results.Causality.DirectEsseRootGodExistence.Solution
public import TruthCore.Results.Causality.DirectEsseRootGodExistence.ExistenceOnly.Solution

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

@[expose] public section

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
    GradesToMaximumAtBeing InAct MoreIn esse :=
  TruthCore.Causality.DirectEsseRootUniquenessAtBeing.restrictGrades InAct MoreIn esse hApproach

/-- Non-corpus helper: `maximumExistsOfExistingRoot` with grades required at esse
only, by instantiating it at the one-point respect type. -/
theorem maximumExistsOfExistingRootAtBeing {W B Respect : Type} (m : Profile W B) (w : W)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop) (esse : Respect)
    (n : B) (hr : ActualRoot m w n)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hApproach : GradesToMaximumAtBeing InAct MoreIn esse)
    (hEM : ExcludedMiddle) : ∃ y, IsMaximumIn InAct MoreIn esse y :=
  maximumExistsOfExistingRoot m w
    (fun x (_ : Unit) => InAct x esse) (fun (_ : Unit) y x => MoreIn esse y x) ()
    n hr hExisting (fun _ => hApproach) hEM

/-- Non-corpus helper: `DirectEsseRootGodExistence.godOfRoot` with grades at esse.
Same calculation: direct esse correspondence identifies every maximum with the
supplied root, and the existing reduced-description theorem names it. -/
theorem godOfRootAtBeing {W B Respect : Type} (m : Profile W B) (w : W)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (PriorSimply ComponentOf : B → B → Prop) (IsGod : B → Prop)
    (n : B) (hr : ActualRoot m w n) (hFirst : IsFirstBeing PriorSimply n)
    (hEM : ExcludedMiddle)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hApproach : GradesToMaximumAtBeing InAct MoreIn esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) :
    IsGod n := by
  have hIdent := maximumEqualsRoot m w InAct MoreIn CausesIn esse n hr
    hEM hGenus hExisting hEsse
  obtain ⟨y, hy⟩ := maximumExistsOfExistingRootAtBeing m w InAct MoreIn esse n hr
    hExisting hApproach hEM
  have hnMax : IsMaximumIn InAct MoreIn esse n := (hIdent y hy) ▸ hy
  have hnScope := hGenus esse n hnMax
  have hFirstMaximum : MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply := by
    intro z hz
    have hEq := hIdent z hz
    subst z
    exact hFirst
  exact TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.reducedDescription
    InAct MoreIn CausesIn esse ComponentOf PriorSimply IsGod
    hBeing hTransfer hNoComponent hFirstMaximum hFull n hnMax hnScope hIdent

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
  obtain ⟨n, hr, _, hFirst⟩ :=
    TruthCore.Results.Causality.NecessaryFirstBeing.necessaryFirst m w PriorSimply
      hPop hWhole hDep hEM hPrior
  exact ⟨n, godOfRootAtBeing m w InAct MoreIn CausesIn esse PriorSimply ComponentOf IsGod
    n hr hFirst hEM hGenus hExisting hEsse hApproach hBeing hTransfer hNoComponent hFull⟩

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
  obtain ⟨n, hr⟩ := TruthCore.Results.Causality.WholeRosterFoundation.actualRootExists
    m w hPop hWhole hEM
  have hFirst : IsFirstBeing PriorSimply n := by
    intro y hy
    rcases hEM (y = n) with hEq | hNe
    · exact hEq
    · exact (hr.2 y (hPrior y n hNe hy)).elim
  exact ⟨n, godOfRootAtBeing m w InAct MoreIn CausesIn esse PriorSimply ComponentOf IsGod
    n hr hFirst hEM hGenus hExisting hEsse hApproach hBeing hTransfer hNoComponent hFull⟩

end TruthCore.Results.Causality.GradesAtBeingRoutes
