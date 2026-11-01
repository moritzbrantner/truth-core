import TruthCore.Causality.GreatestDegreeRootRoute
import TruthCore.Causality.ActualCommonRoot
import TruthCore.Causality.NecessaryConcreteRouteBridge
import TruthCore.Causality.ExistenceActuality
import TruthCore.Causality.WholeRosterFoundation

import TruthCore.Results.Causality.WholeRosterFoundation.Solution
import TruthCore.Results.Causality.ActualCommonRoot.Solution
import TruthCore.Results.Causality.ActualRootNecessityUpgrade.Solution

namespace TruthCore.Results.Causality.GreatestDegreeRootRoute
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.WholeRosterFoundation (WholeRosterNotTrapped)
open TruthCore.Causality.ActualCommonRoot (ActualCommonRootAt)
open TruthCore.Causality.GreatestDegreeRootRoute (GreatestBeingDegreeAttained)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- Non-corpus pointwise helper: compare this supplied actual root with a
supplied greatest bearer. It preserves B, w, InAct and CausesIn exactly. -/
theorem greatestEqualsRoot {W B R Degree : Type} [Preorder Degree]
    (m : Profile W B) (w : W) (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) (value : B → Degree)
    (n : B) (hr : TruthCore.Causality.NecessaryRootFork.ActualRoot m w n)
    (hEM : ExcludedMiddle) (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hGenus : GreatestDegreeCausesAllInGenusReading InAct CausesIn esse value) :
    ∀ g, GreatestDegreeBearer InAct esse value g → g = n := by
  intro g hg
  cases hEM (g = n) with
  | inl hSame => exact hSame
  | inr hOther =>
    exact False.elim (hr.2 g (hEsse g n hOther hr.1
      (hGenus g hg n (fun h => hOther h.symm) (hExisting n hr.1.2))))

/-- Seven explicit inputs give the existing common actual root at the SAME
world and grounding relation. Greatest attainment and its causal principle
replace the old weak H/strong I pair; no bundle weakening is asserted. -/
theorem commonRoot {W B R Degree : Type} [Preorder Degree]
    (m : Profile W B) (w : W) (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) (value : B → Degree)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w) (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hAttained : GreatestBeingDegreeAttained InAct esse value)
    (hGenus : GreatestDegreeCausesAllInGenusReading InAct CausesIn esse value) :
    ActualCommonRootAt m w := by
  obtain ⟨n, hn⟩ :=
    TruthCore.Results.Causality.WholeRosterFoundation.actualRootExists m w hPop hWhole hEM
  obtain ⟨g, hg⟩ := hAttained
  have heq := greatestEqualsRoot m w InAct CausesIn esse value n hn
    hEM hExisting hEsse hGenus g hg
  subst g
  refine ⟨n, hn, ?_⟩
  intro x hx
  cases hEM (x = n) with
  | inl hSame => exact Or.inl hSame
  | inr hOther =>
    exact Or.inr (hEsse n x (fun h => hOther h.symm) hx
      (hGenus n hg x hOther (hExisting x hx.2)))

/-- Non-corpus composition: the old uniqueness projection and necessity
upgrade preserve the root supplied by commonRoot. C is retained explicitly;
no greatestness-to-modal-necessity inference or extra registered endpoint. -/
theorem necessaryRoot {W B R Degree : Type} [Preorder Degree]
    (m : Profile W B) (w : W) (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) (value : B → Degree)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w) (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hAttained : GreatestBeingDegreeAttained InAct esse value)
    (hGenus : GreatestDegreeCausesAllInGenusReading InAct CausesIn esse value)
    (hDep : TruthCore.Causality.BruteFoundationBoundary.EveryContingentGroundedAt m w) :
    TruthCore.Causality.NecessaryRootUniqueness.UniqueNecessaryActualRootAt m w :=
  TruthCore.Results.Causality.ActualRootNecessityUpgrade.upgrade m w
    (TruthCore.Results.Causality.ActualCommonRoot.uniqueRoot m w
      (commonRoot m w InAct CausesIn esse value hPop hWhole hEM
        hExisting hEsse hAttained hGenus)) hDep hEM

end TruthCore.Results.Causality.GreatestDegreeRootRoute
