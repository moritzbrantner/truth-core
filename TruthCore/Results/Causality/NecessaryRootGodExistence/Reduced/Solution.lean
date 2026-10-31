import TruthCore.Results.Causality.NecessaryFirstBeing.Solution
import TruthCore.Results.Causality.NecessaryRootGodExistence.Solution
import TruthCore.Causality.NecessaryRootUniqueness
import TruthCore.Case.Catholicism.CausalPerfectionTransfer

namespace TruthCore.Results.Causality.NecessaryRootGodExistence.Reduced

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

/-- Non-corpus witness-preserving helper. Necessary existence supplies actual
esse through the retained necessary-being/being bridge. The existing actual fork
then supplies a maximum under grades-to-maximum, without truth or noble grades.
The supplied-root convergence calculation names that same necessary first root. -/
theorem sameWitnessGod {W B Respect : Type} (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (PriorSimply ComponentOf : B → B → Prop) (IsGod : B → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hBridge : NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hHasBeing : NecessaryBeingHasBeing (modalPossible m w) (modalIsAt m) InAct esse)
    (hCause : CauseOfNecessaryBeingCausesItsNecessity (modalPossible m w) (modalIsAt m)
      CausesIn esse CausesNecessityOf)
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
  have hMaximum := TruthCore.Causality.NecessaryRootUniqueness.maximumExistsOfNecessaryAt
    m w InAct MoreIn esse n hn hHasBeing hApproach hEM
  have hGod := TruthCore.Results.Causality.NecessaryRootGodExistence.godOfRootAndMaximum
    m w CausesNecessityOf InAct MoreIn CausesIn esse PriorSimply ComponentOf IsGod
    n hr hn hFirst hEM hBridge hGenus hHasBeing hCause hBeing hTransfer hNoComponent hFull
    hMaximum
  exact ⟨n, hr, hn, hFirst, hGod⟩

/-- GodExists from the fourteen retained inputs. The proof derives structured
naming antecedents for the same actual necessary witness; it does not independently
establish the metaphysical premises or the retained nominal identification. -/
theorem godExists {W B Respect : Type} (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (PriorSimply ComponentOf : B → B → Prop) (IsGod : B → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hBridge : NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hHasBeing : NecessaryBeingHasBeing (modalPossible m w) (modalIsAt m) InAct esse)
    (hCause : CauseOfNecessaryBeingCausesItsNecessity (modalPossible m w) (modalIsAt m)
      CausesIn esse CausesNecessityOf)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) :
    GodExists IsGod := by
  obtain ⟨n, _, _, _, hGod⟩ := sameWitnessGod m w CausesNecessityOf
    InAct MoreIn CausesIn esse PriorSimply ComponentOf IsGod
    hPop hWhole hDep hEM hPrior hBridge hGenus hHasBeing hCause hApproach
    hBeing hTransfer hNoComponent hFull
  exact ⟨n, hGod⟩

end TruthCore.Results.Causality.NecessaryRootGodExistence.Reduced
