import TruthCore.Causality.ActualCommonRoot
import TruthCore.Causality.ActualRootUniqueness
import TruthCore.Causality.DirectEsseRootUniquenessAtBeing
import TruthCore.Results.Causality.WholeRosterFoundation.Solution

namespace TruthCore.Results.Causality.ActualCommonRoot
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.WholeRosterFoundation (WholeRosterNotTrapped)
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing (GradesToMaximumAtBeing)
open TruthCore.Causality.ActualRootUniqueness (UniqueActualRootAt)
open TruthCore.Causality.ActualCommonRoot
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- Same seven premises give DIRECT common actual-ground coverage, without
contingent dependence or a modal-necessity conclusion. -/
theorem commonRoot {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w) (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hApproach : GradesToMaximumAtBeing InAct MoreIn esse) : ActualCommonRootAt m w := by
  obtain ⟨n, hn⟩ :=
    TruthCore.Results.Causality.WholeRosterFoundation.actualRootExists m w hPop hWhole hEM
  -- Only the respect carrier is restricted; all being/world/esse dictionaries stay.
  let act : B → Unit → Prop := fun x _ => InAct x esse
  let more : Unit → B → B → Prop := fun _ y x => MoreIn esse y x
  let cause : B → B → Unit → Prop := fun c x _ => CausesIn c x esse
  obtain ⟨maximum, hMaximum⟩ :=
    TruthCore.Causality.DirectEsseRootRoute.maximumExistsOfExistingRoot
      m w act more () n hn hExisting (fun _ => hApproach) hEM
  have heq := TruthCore.Causality.DirectEsseRootRoute.maximumEqualsRoot
    m w act more cause () n hn hEM (fun _ => hGenus) hExisting hEsse maximum hMaximum
  subst maximum
  refine ⟨n, hn, ?_⟩
  intro x hx
  cases hEM (x = n) with
  | inl hSame => exact Or.inl hSame
  | inr hOther =>
    exact Or.inr (hEsse n x (fun he => hOther he.symm) hx
      (hGenus n hMaximum x hOther (hExisting x hx.2)))

/-- Common coverage excludes a second actual root constructively, since an
incoming ground contradicts its roothood. No extra EM or C input is used. -/
theorem uniqueRoot {W B : Type} (m : Profile W B) (w : W)
    (hCommon : ActualCommonRootAt m w) : UniqueActualRootAt m w := by
  obtain ⟨n, hn, hCover⟩ := hCommon
  refine ⟨n, hn, ?_⟩
  intro x hx
  cases hCover x hx.1 with
  | inl hSame => exact hSame
  | inr hGround => exact False.elim (hx.2 n hGround)

end TruthCore.Results.Causality.ActualCommonRoot
