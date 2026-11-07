module

public import TruthCore.Causality.Round2ExistenceAct

@[expose] public section

namespace TruthCore.Results.Causality.Round2ExistenceAct
open TruthCore.Causality.Round2ExistenceAct
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect (OperationAttribution)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.OperationFollowsBeing
open TruthCore.Causality.ExistenceActuality
open TruthCore.Logic.CogitoEsse
open TruthCore.Logic.CogitoConcrete
open TruthCore.Logic.CogitoSubject
open TruthCore.Logic

/-! ## Map 1: the esse contract -/

/-- An existent at `w` is in act in some respect `r`; whatever is in act in some
respect is in act of esse (q.4 a.1 ad 3 reading). Two OPEN-or-read premises. -/
theorem existingInActAtFromSomeAct {W B R : Type} (m : Ontic W B)
    (InAct : B → R → Prop) (esse : R) (w : W)
    (hSome : ExistentInActInSomeRespectAt m InAct w)
    (hOnly : ActualityOnlyInsofarAsBeingReading InAct esse) :
    ExistingInActAt m InAct esse w := by
  intro x hx
  obtain ⟨r, hr⟩ := hSome x hx
  exact hOnly x r hr

/-- The Eleatic route: every existent has causal power, power only insofar as
in act (q.25 a.1 reading), actuality only insofar as being. -/
theorem existingInActAtFromEleaticPower {W B R : Type} (m : Ontic W B)
    (hasCausalPower : W → B → Prop) (InAct : B → R → Prop) (esse : R) (w : W)
    (hPow : EveryExistentHasCausalPowerAt m hasCausalPower w)
    (hAct : ActivePowerOnlyInsofarAsInActReading hasCausalPower InAct w)
    (hOnly : ActualityOnlyInsofarAsBeingReading InAct esse) :
    ExistingInActAt m InAct esse w := by
  intro x hx
  obtain ⟨r, hr⟩ := hAct x (hPow x hx)
  exact hOnly x r hr

/-- The classical route through the merely possible: if `x` exists at `w` and
were not in act of esse, it would be merely possible and so not exist at `w`.
Excluded middle on `InAct x esse` closes the case. -/
theorem existingInActAtFromMerePossibility {W B R : Type} (m : Ontic W B)
    (InAct : B → R → Prop) (esse : R) (MerelyPossible : B → Prop) (w : W)
    (hEM : ExcludedMiddle)
    (hLack : LackingEsseIsMerelyPossible InAct esse MerelyPossible)
    (hMP : MerelyPossibleNotExistentAt m MerelyPossible w) :
    ExistingInActAt m InAct esse w := by
  intro x hx
  cases hEM (InAct x esse) with
  | inl h => exact h
  | inr h => exact absurd hx (hMP x (hLack x h))

/-- The intermediate Eleatic step: every existent is in act in some respect. -/
theorem existentInActFromEleaticPower {W B R : Type} (m : Ontic W B)
    (hasCausalPower : W → B → Prop) (InAct : B → R → Prop) (w : W)
    (hPow : EveryExistentHasCausalPowerAt m hasCausalPower w)
    (hAct : ActivePowerOnlyInsofarAsInActReading hasCausalPower InAct w) :
    ExistentInActInSomeRespectAt m InAct w := by
  intro x hx
  have hp : hasCausalPower w x := hPow x hx
  exact hAct x hp

/-! ## Map 2: intellectual exercise requires act -/

/-- Intellectual exercise is operating; operating only of a being in act. -/
theorem intellectualExerciseRequiresActFromOperating {B Episode R : Type}
    (a : OperationAttribution B Episode) (Operates : B → Prop) (InAct : B → R → Prop)
    (hOp : IntellectualExerciseIsOperating a Operates)
    (hOnly : OperatingOnlyOfBeingInAct Operates InAct) :
    IntellectualExerciseRequiresAct a InAct := by
  intro b e h
  have hb : Operates b := hOp b e h
  exact hOnly b hb

/-- The exerciser has active power; power only insofar as in act. -/
theorem intellectualExerciseRequiresActFromActivePower {W B Episode R : Type}
    (a : OperationAttribution B Episode) (hasCausalPower : W → B → Prop)
    (InAct : B → R → Prop) (w : W)
    (hPow : IntellectualExerciserHasPowerAt a hasCausalPower w)
    (hAct : ActivePowerOnlyInsofarAsInActReading hasCausalPower InAct w) :
    IntellectualExerciseRequiresAct a InAct := by
  intro b e h
  have hp : hasCausalPower w b := hPow b e h
  exact hAct b hp

/-- The exerciser causes something (the inner word); causing only of a being
in act (q.75 a.2 reading). -/
theorem intellectualExerciseRequiresActFromProduction {W B Episode R : Type}
    (o : Ontic W B) (a : OperationAttribution B Episode) (InAct : B → R → Prop) (w : W)
    (hProd : IntellectualExerciseProducesAt o a w)
    (hOp : OperationOnlyOfBeingInActReading o InAct w) :
    IntellectualExerciseRequiresAct a InAct := by
  intro b e h
  obtain ⟨y, hy⟩ := hProd b e h
  exact hOp b y hy

/-- The exerciser exists at `w`; every existent at `w` is in act of esse. -/
theorem intellectualExerciseRequiresActFromExistence {W B Episode R : Type}
    (m : Ontic W B) (a : OperationAttribution B Episode) (InAct : B → R → Prop)
    (esse : R) (w : W)
    (hEx : IntellectualExerciserExistsAt m a w)
    (hEsse : ExistingInActAt m InAct esse w) :
    IntellectualExerciseRequiresAct a InAct := by
  intro b e h
  have hb : m.ExistsAt w b := hEx b e h
  exact ⟨esse, hEsse b hb⟩

/-! ## Map 3: occurring thought is intellectual exercise -/

/-- Every occurring thought is intellective; bearing an intellective episode is
exercising intellect in it. -/
theorem thoughtIsExerciseFromIntellective {B Episode : Type}
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (Intellective : Episode → Prop) (a : OperationAttribution B Episode)
    (hInt : OccurringThoughtIsIntellective Occurs Intellective)
    (hBear : BearingIntellectiveEpisodeIsExercise Bears Intellective a) :
    BorneThoughtExercisesIntellect Occurs Bears a := by
  intro b e ho hb
  have hi : Intellective e := hInt e ho
  exact hBear b e hi hb

/-- The bearer opines the borne thought's content; a bearer opining the content
of its episode exercises intellect in it. -/
theorem thoughtIsExerciseFromOpining {B Episode : Type}
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (Opines : B → Prop → Prop) (content : Episode → Prop)
    (a : OperationAttribution B Episode)
    (hOpin : BorneThoughtIsOpining Occurs Bears Opines content)
    (hJudge : OpiningBorneContentIsIntellectualExercise Bears Opines content a) :
    BorneThoughtExercisesIntellect Occurs Bears a := by
  intro b e ho hb
  have hop : Opines b (content e) := hOpin b e ho hb
  exact hJudge b e hb hop

/-! ## Map 4: the bearer exists at the selected world -/

/-- Thought is intellectual exercise, exercise requires act, act only insofar
as esse, and esse suffices for existence at `w`. -/
theorem bearerExistsFromOperationAndEsse {W B Episode R : Type}
    (m : Ontic W B) (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (a : OperationAttribution B Episode) (InAct : B → R → Prop) (esse : R) (w : W)
    (hThought : BorneThoughtExercisesIntellect Occurs Bears a)
    (hReq : IntellectualExerciseRequiresAct a InAct)
    (hOnly : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hSuff : ActOfEsseSufficesForExistenceAt m InAct esse w) :
    EveryBearerExistsAt m Occurs Bears w := by
  intro b e ho hb
  obtain ⟨r, hr⟩ := hReq b e (hThought b e ho hb)
  exact hSuff b (hOnly b r hr)

/-- Occurring episodes occur at `w`; bearers exist where their episodes occur. -/
theorem bearerExistsFromWorldIndexedOccurrence {W B Episode : Type}
    (m : Ontic W B) (Occurs : Episode → Prop) (OccursAt : W → Episode → Prop)
    (Bears : B → Episode → Prop) (w : W)
    (hAt : OccurringThoughtOccursAt OccursAt Occurs w)
    (hWhere : BearerExistsWhereEpisodeOccurs m OccursAt Bears) :
    EveryBearerExistsAt m Occurs Bears w := by
  intro b e ho hb
  have hw : OccursAt w e := hAt e ho
  exact hWhere w b e hw hb

/-! ## Map 5: the bearer principle -/

/-- Every occurring thought is a modification; no modification without a bearer. -/
theorem everyThoughtHasSubjectFromModification {S Episode : Type}
    (Occurs : Episode → Prop) (Bears : S → Episode → Prop)
    (Modification : Episode → Prop)
    (hMod : OccurringThoughtIsModification Occurs Modification)
    (hNo : NoModificationWithoutBearer Modification Bears) :
    EveryThoughtHasSubject Occurs Bears := by
  intro e ho
  have hm : Modification e := hMod e ho
  exact hNo e hm

/-- Every occurring thought is an operation; every operation has an agent; the
agent of an episode bears it. -/
theorem everyThoughtHasSubjectFromAgency {S Episode : Type}
    (Occurs : Episode → Prop) (Bears : S → Episode → Prop)
    (IsOperation : Episode → Prop) (AgentOf : S → Episode → Prop)
    (hOper : OccurringThoughtIsOperation Occurs IsOperation)
    (hAgent : EveryOperationHasAgent IsOperation AgentOf)
    (hBears : AgentOfEpisodeBearsIt AgentOf Bears) :
    EveryThoughtHasSubject Occurs Bears := by
  intro e ho
  obtain ⟨s, hs⟩ := hAgent e (hOper e ho)
  exact ⟨s, hBears s e hs⟩

/-! ## Controls -/

section Controls
open TruthCore.Causality.Round2ExistenceAct.Control

macro "ctrl" : tactic => `(tactic| (
  delta ExistentInActInSomeRespectAt EveryExistentHasCausalPowerAt LackingEsseIsMerelyPossible
    MerelyPossibleNotExistentAt IntellectualExerciseIsOperating OperatingOnlyOfBeingInAct
    IntellectualExerciserHasPowerAt IntellectualExerciseProducesAt IntellectualExerciserExistsAt
    OccurringThoughtIsIntellective BearingIntellectiveEpisodeIsExercise
    OpiningBorneContentIsIntellectualExercise ActOfEsseSufficesForExistenceAt
    OccurringThoughtOccursAt BearerExistsWhereEpisodeOccurs OccurringThoughtIsModification
    NoModificationWithoutBearer OccurringThoughtIsOperation EveryOperationHasAgent
    AgentOfEpisodeBearsIt ExistingInActAt ActualityOnlyInsofarAsBeingReading
    ActivePowerOnlyInsofarAsInActReading OperationOnlyOfBeingInActReading
    IntellectualExerciseRequiresAct BorneThoughtExercisesIntellect BorneThoughtIsOpining
    EveryBearerExistsAt EveryThoughtHasSubject ThoughtOccurs
  decide))

theorem omitSomeAct_holds : omitSomeAct := by delta omitSomeAct; ctrl
theorem omitActualityOnly1_holds : omitActualityOnly1 := by delta omitActualityOnly1; ctrl
theorem omitEleatic_holds : omitEleatic := by delta omitEleatic; ctrl
theorem omitActivePower1_holds : omitActivePower1 := by delta omitActivePower1; ctrl
theorem omitActualityOnly2_holds : omitActualityOnly2 := by delta omitActualityOnly2; ctrl
theorem omitLackingEsse_holds : omitLackingEsse := by delta omitLackingEsse; ctrl
theorem omitMerelyPossible_holds : omitMerelyPossible := by delta omitMerelyPossible; ctrl
theorem omitEleatic2_holds : omitEleatic2 := by delta omitEleatic2; ctrl
theorem omitActivePower2_holds : omitActivePower2 := by delta omitActivePower2; ctrl
theorem omitExerciseIsOperating_holds : omitExerciseIsOperating := by delta omitExerciseIsOperating; ctrl
theorem omitOperatingOnlyInAct_holds : omitOperatingOnlyInAct := by delta omitOperatingOnlyInAct; ctrl
theorem omitExerciserPower_holds : omitExerciserPower := by delta omitExerciserPower; ctrl
theorem omitActivePower3_holds : omitActivePower3 := by delta omitActivePower3; ctrl
theorem omitProduces_holds : omitProduces := by delta omitProduces; ctrl
theorem omitOperationOnlyInAct_holds : omitOperationOnlyInAct := by delta omitOperationOnlyInAct; ctrl
theorem omitExerciserExists_holds : omitExerciserExists := by delta omitExerciserExists; ctrl
theorem omitExistingInAct_holds : omitExistingInAct := by delta omitExistingInAct; ctrl
theorem omitIntellective_holds : omitIntellective := by delta omitIntellective; ctrl
theorem omitBearingIntellective_holds : omitBearingIntellective := by delta omitBearingIntellective; ctrl
theorem omitBorneOpining_holds : omitBorneOpining := by delta omitBorneOpining; ctrl
theorem omitOpiningIsExercise_holds : omitOpiningIsExercise := by delta omitOpiningIsExercise; ctrl
theorem omitThoughtIsExercise_holds : omitThoughtIsExercise := by delta omitThoughtIsExercise; ctrl
theorem omitExerciseRequiresAct_holds : omitExerciseRequiresAct := by delta omitExerciseRequiresAct; ctrl
theorem omitActualityOnly3_holds : omitActualityOnly3 := by delta omitActualityOnly3; ctrl
theorem omitEsseSuffices_holds : omitEsseSuffices := by delta omitEsseSuffices; ctrl
theorem omitOccursAt_holds : omitOccursAt := by delta omitOccursAt; ctrl
theorem omitBearerWhere_holds : omitBearerWhere := by delta omitBearerWhere; ctrl
theorem omitModification_holds : omitModification := by delta omitModification; ctrl
theorem omitNoModWithoutBearer_holds : omitNoModWithoutBearer := by delta omitNoModWithoutBearer; ctrl
theorem omitIsOperation_holds : omitIsOperation := by delta omitIsOperation; ctrl
theorem omitHasAgent_holds : omitHasAgent := by delta omitHasAgent; ctrl
theorem omitAgentBears_holds : omitAgentBears := by delta omitAgentBears; ctrl
theorem witness_holds : witness := by
  delta witness
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ctrl

/-- The batch controls: one omission model per premise of each derivation
(excluded middle excepted) and one joint nonvacuity witness. -/
theorem controls : Certificate :=
  ⟨omitSomeAct_holds,
   omitActualityOnly1_holds,
   omitEleatic_holds,
   omitActivePower1_holds,
   omitActualityOnly2_holds,
   omitLackingEsse_holds,
   omitMerelyPossible_holds,
   omitEleatic2_holds,
   omitActivePower2_holds,
   omitExerciseIsOperating_holds,
   omitOperatingOnlyInAct_holds,
   omitExerciserPower_holds,
   omitActivePower3_holds,
   omitProduces_holds,
   omitOperationOnlyInAct_holds,
   omitExerciserExists_holds,
   omitExistingInAct_holds,
   omitIntellective_holds,
   omitBearingIntellective_holds,
   omitBorneOpining_holds,
   omitOpiningIsExercise_holds,
   omitThoughtIsExercise_holds,
   omitExerciseRequiresAct_holds,
   omitActualityOnly3_holds,
   omitEsseSuffices_holds,
   omitOccursAt_holds,
   omitBearerWhere_holds,
   omitModification_holds,
   omitNoModWithoutBearer_holds,
   omitIsOperation_holds,
   omitHasAgent_holds,
   omitAgentBears_holds,
   witness_holds⟩

end Controls

end TruthCore.Results.Causality.Round2ExistenceAct
