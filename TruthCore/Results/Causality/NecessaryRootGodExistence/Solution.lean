import TruthCore.Results.Causality.NecessaryFirstBeing.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia.Solution
import TruthCore.Case.Catholicism.CausalPerfectionTransfer

namespace TruthCore.Results.Causality.NecessaryRootGodExistence

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

/-- Structured naming antecedents for a supplied actual necessary first root
and an independently supplied maximum. Uniqueness is derived from convergence,
not added as another premise. The nominal identification remains open. -/
theorem godOfRootAndMaximum {W B Respect : Type} (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (PriorSimply ComponentOf : B → B → Prop) (IsGod : B → Prop)
    (n : B) (hr : ActualRoot m w n) (hn : NecessaryAt m.ontic w n)
    (hFirst : IsFirstBeing PriorSimply n) (hEM : ExcludedMiddle)
    (hBridge : NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hHasBeing : NecessaryBeingHasBeing (modalPossible m w) (modalIsAt m) InAct esse)
    (hCause : CauseOfNecessaryBeingCausesItsNecessity (modalPossible m w) (modalIsAt m)
      CausesIn esse CausesNecessityOf)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod)
    (hMaximum : ∃ y, IsMaximumIn InAct MoreIn esse y) : IsGod n := by
  obtain ⟨_, hIdent⟩ := necessaryRootIsMaximumOfRoot m w CausesNecessityOf
    InAct MoreIn CausesIn esse n hr hn hEM hBridge hGenus hHasBeing hCause
  obtain ⟨y, hy⟩ := hMaximum
  have hnMax : IsMaximumIn InAct MoreIn esse n := (hIdent y hy) ▸ hy
  have hnScope := hGenus esse n hnMax
  have hnEvery : CausesEveryPerfectionOfOthers InAct CausesIn n :=
    fun x r hOther hAct => hTransfer n hnScope x r hOther
      (hnScope x hOther (hBeing x r hAct)) hAct
  have hnRemote : RemoteFromAll ComponentOf n :=
    fun x hComponent => hNoComponent n x hComponent hFirst
  exact hFull n hnMax hnScope hnEvery hnRemote hIdent

/-- Non-corpus helper retaining the actual necessary first root through naming.
The maximum supplied by the quarta via is identified with this root by the
existing convergence theorem; no fresh maximum or uniqueness premise is added.
The final full-description naming application retains its open nominal bridge.
Neither unique necessary individuality nor a converse from God is asserted. -/
theorem sameWitnessGod {W B Respect : Type} (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (bonum verum nobile esse : Respect)
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
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hTrue : MostTrueIsMostBeingReading InAct MoreIn verum esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) :
    ∃ n, ActualRoot m w n ∧ NecessaryAt m.ontic w n ∧
      IsFirstBeing PriorSimply n ∧ IsGod n := by
  obtain ⟨n, hr, hn, hFirst⟩ :=
    TruthCore.Results.Causality.NecessaryFirstBeing.necessaryFirst m w PriorSimply
      hPop hWhole hDep hEM hPrior
  obtain ⟨y, hy, _⟩ :=
    TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia.quartaVia
      InAct MoreIn CausesIn bonum verum nobile esse hGrades hApproach hTrue hGenus
  have hGod := godOfRootAndMaximum m w CausesNecessityOf InAct MoreIn CausesIn esse
    PriorSimply ComponentOf IsGod n hr hn hFirst hEM hBridge hGenus hHasBeing hCause
    hBeing hTransfer hNoComponent hFull ⟨y, hy⟩
  exact ⟨n, hr, hn, hFirst, hGod⟩

/-- Project existing GodExists from the same actual necessary first witness.
Structured antecedents are derived by imported proofs; the final nominal naming
bridge remains an explicit open commitment, not a new proof of its truth. -/
theorem godExists {W B Respect : Type} (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (bonum verum nobile esse : Respect)
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
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hTrue : MostTrueIsMostBeingReading InAct MoreIn verum esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hTransfer : UniversalCauseTransfersPerfections InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) :
    GodExists IsGod := by
  obtain ⟨n, _, _, _, hGod⟩ := sameWitnessGod m w CausesNecessityOf
    InAct MoreIn CausesIn bonum verum nobile esse PriorSimply ComponentOf IsGod
    hPop hWhole hDep hEM hPrior hBridge hGenus hHasBeing hCause hGrades hApproach hTrue
    hBeing hTransfer hNoComponent hFull
  exact ⟨n, hGod⟩

end TruthCore.Results.Causality.NecessaryRootGodExistence
