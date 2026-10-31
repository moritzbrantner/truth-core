import TruthCore.Results.Causality.RootIntellectWill.Solution
import TruthCore.Results.Causality.RootNonlimitationFromCompositionKinds.Solution
import TruthCore.Results.Causality.RootIntellectWillOmission.Solution
import TruthCore.Causality.RootIntellectWill
import TruthCore.Results.Causality.RootWithoutLimitingPrinciple.Solution
import TruthCore.Results.Causality.RootEssenceIdentity.Solution

namespace TruthCore.Results.Causality.RootIntellectWillReduced
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.RootEssenceIdentity
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
  (DistinctEsseCauseDichotomyReading EssentialPrinciplesCannotCauseDistinctEsseReading)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

open TruthCore.Causality.RootWithoutLimitingPrinciple
open TruthCore.Causality.RootMultiplication (HasLimitingPrinciple)
open TruthCore.Causality.NecessaryConcreteRouteBridge (SimplyPriorIsActualConcreteGround)
open TruthCore.Latin.Aquinas.SummaTheologiae

open TruthCore.Causality.RootIntellectWill
open TruthCore.Case.Catholicism (IsSimple RemoteFromAll)
theorem necessaryRootIntellectWill {W B P R : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop) (Composite MatterForm HasIntellect HasWill : B → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hPosterior : CompositePosteriorToComponentsReading ComponentOf PriorSimply)
    (hOther : CompositeHasComponentOtherThanItselfReading Composite ComponentOf)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite p.essenceOf p.esseOf)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hIntellect : ImmaterialIsIntellectualReading MatterForm HasIntellect ComponentOf)
    (hWill : WillFollowsIntellectReading HasIntellect HasWill) :
    NecessaryRootIntellectWillAt m w p PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill := by
  have hRoot :=
    TruthCore.Results.Causality.RootNonlimitationFromCompositionKinds.necessaryRootWithoutLimitingPrinciple
      m w p PriorSimply ComponentOf Composite MatterForm
      hPop hWhole hDep hEM hPrior hPosterior hOther hKinds
  exact TruthCore.Results.Causality.RootIntellectWill.ofNonlimitation
    m w p PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill
    hEM hRoot hKinds hNoComponent hIntellect hWill

open TruthCore.Causality.RootIntellectWillOmission
open TruthCore.Causality.NecessarySimplePlurality

/-- Project the exact nine remaining nonlogical interfaces from the ORIGINAL
ledger-L omission control. EM is supplied separately. No new interpretation,
countermodel or attribute assignment is introduced. -/
theorem reducedOmissionInputs (hEM : ExcludedMiddle) :
    TruthCore.Causality.RootIntellectWillOmission.Control ∧
    (InhabitedConcreteAt model.ontic model.concrete false ∧
      WholeRosterNotTrapped model false ∧ EveryContingentGroundedAt model false ∧
      SimplyPriorIsActualConcreteGround model false component ∧
      CompositePosteriorToComponentsReading component component ∧
      CompositeHasComponentOtherThanItselfReading composite component ∧
      MatterFormAndEsseEssenceAreCompositionsReading matterForm composite essence esse ∧
      ImmaterialIsIntellectualReading matterForm noIntellect component ∧
      WillFollowsIntellectReading noIntellect noWill) := by
  have hControl := TruthCore.Results.Causality.RootIntellectWillOmission.checks hEM
  rcases hControl.2.1 with ⟨hPop, hWhole, hDep, _, _, _, _, hPrior,
    hPosterior, hOther, hKinds, hIntellect, hWill⟩
  exact ⟨hControl, hPop, hWhole, hDep, hPrior, hPosterior, hOther, hKinds, hIntellect, hWill⟩

end TruthCore.Results.Causality.RootIntellectWillReduced
