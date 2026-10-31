import TruthCore.Causality.DirectEsseRootRoute
import TruthCore.Results.Causality.NecessaryFirstBeing.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.Solution

namespace TruthCore.Results.Causality.DirectEsseRootGodExistence

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

/-- Non-corpus structured naming calculation for a supplied actual first root.
Direct esse correspondence identifies every maximum with the supplied n; the
existing reduced-description theorem derives its naming antecedents. The nominal
identification remains explicit. No modal existence premise is needed here. -/
theorem godOfRoot {W B Respect : Type} (m : Profile W B) (w : W)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (PriorSimply ComponentOf : B → B → Prop) (IsGod : B → Prop)
    (n : B) (hr : ActualRoot m w n) (hFirst : IsFirstBeing PriorSimply n)
    (hEM : ExcludedMiddle)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) :
    IsGod n := by
  have hIdent := maximumEqualsRoot m w InAct MoreIn CausesIn esse n hr
    hEM hGenus hExisting hEsse
  obtain ⟨y, hy⟩ := maximumExistsOfExistingRoot m w InAct MoreIn esse n hr
    hExisting hApproach hEM
  have hnMax : IsMaximumIn InAct MoreIn esse n := (hIdent y hy) ▸ hy
  have hnScope := hGenus esse n hnMax
  have hFirstMaximum : MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply := by
    intro z hz
    have hEq := hIdent z hz
    subst z
    exact hFirst
  have hNaming :=
    TruthCore.Results.Aquinas.SummaTheologiae.CausalPerfectionTransfer.reducedDescription
      InAct MoreIn CausesIn esse ComponentOf PriorSimply IsGod
      hBeing hTransfer hNoComponent hFirstMaximum hFull
  exact hNaming n hnMax hnScope hIdent

/-- Preserve the same actual necessary first root through the alternate direct
esse correspondence. The correspondence covers actual concrete targets, including
contingent ones; it is not asserted weaker than the necessity-cause package. -/
theorem sameWitnessGod {W B Respect : Type} (m : Profile W B) (w : W)
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
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) :
    ∃ n, ActualRoot m w n ∧ NecessaryAt m.ontic w n ∧
      IsFirstBeing PriorSimply n ∧ IsGod n := by
  obtain ⟨n, hr, hn, hFirst⟩ :=
    TruthCore.Results.Causality.NecessaryFirstBeing.necessaryFirst m w PriorSimply
      hPop hWhole hDep hEM hPrior
  have hGod := godOfRoot m w InAct MoreIn CausesIn esse PriorSimply ComponentOf IsGod
    n hr hFirst hEM hGenus hExisting hEsse hApproach hBeing hTransfer hNoComponent hFull
  exact ⟨n, hr, hn, hFirst, hGod⟩

/-- Existing GodExists from thirteen explicit inputs. Necessity of the same
named root is preserved in the helper; no causal correspondence, nominal naming
bridge or other philosophical premise is independently defended here. -/
theorem godExists {W B Respect : Type} (m : Profile W B) (w : W)
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
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) :
    GodExists IsGod := by
  obtain ⟨n, _, _, _, hGod⟩ := sameWitnessGod m w InAct MoreIn CausesIn esse
    PriorSimply ComponentOf IsGod hPop hWhole hDep hEM hPrior hGenus hExisting hEsse
    hApproach hBeing hTransfer hNoComponent hFull
  exact ⟨n, hGod⟩

end TruthCore.Results.Causality.DirectEsseRootGodExistence
