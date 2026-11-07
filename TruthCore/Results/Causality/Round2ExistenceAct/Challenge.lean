import TruthCore.Causality.Round2ExistenceAct

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
  sorry

/-- The Eleatic route: every existent has causal power, power only insofar as
in act (q.25 a.1 reading), actuality only insofar as being. -/
theorem existingInActAtFromEleaticPower {W B R : Type} (m : Ontic W B)
    (hasCausalPower : W → B → Prop) (InAct : B → R → Prop) (esse : R) (w : W)
    (hPow : EveryExistentHasCausalPowerAt m hasCausalPower w)
    (hAct : ActivePowerOnlyInsofarAsInActReading hasCausalPower InAct w)
    (hOnly : ActualityOnlyInsofarAsBeingReading InAct esse) :
    ExistingInActAt m InAct esse w := by
  sorry

/-- The classical route through the merely possible: if `x` exists at `w` and
were not in act of esse, it would be merely possible and so not exist at `w`.
Excluded middle on `InAct x esse` closes the case. -/
theorem existingInActAtFromMerePossibility {W B R : Type} (m : Ontic W B)
    (InAct : B → R → Prop) (esse : R) (MerelyPossible : B → Prop) (w : W)
    (hEM : ExcludedMiddle)
    (hLack : LackingEsseIsMerelyPossible InAct esse MerelyPossible)
    (hMP : MerelyPossibleNotExistentAt m MerelyPossible w) :
    ExistingInActAt m InAct esse w := by
  sorry

/-- The intermediate Eleatic step: every existent is in act in some respect. -/
theorem existentInActFromEleaticPower {W B R : Type} (m : Ontic W B)
    (hasCausalPower : W → B → Prop) (InAct : B → R → Prop) (w : W)
    (hPow : EveryExistentHasCausalPowerAt m hasCausalPower w)
    (hAct : ActivePowerOnlyInsofarAsInActReading hasCausalPower InAct w) :
    ExistentInActInSomeRespectAt m InAct w := by
  sorry

/-! ## Map 2: intellectual exercise requires act -/

/-- Intellectual exercise is operating; operating only of a being in act. -/
theorem intellectualExerciseRequiresActFromOperating {B Episode R : Type}
    (a : OperationAttribution B Episode) (Operates : B → Prop) (InAct : B → R → Prop)
    (hOp : IntellectualExerciseIsOperating a Operates)
    (hOnly : OperatingOnlyOfBeingInAct Operates InAct) :
    IntellectualExerciseRequiresAct a InAct := by
  sorry

/-- The exerciser has active power; power only insofar as in act. -/
theorem intellectualExerciseRequiresActFromActivePower {W B Episode R : Type}
    (a : OperationAttribution B Episode) (hasCausalPower : W → B → Prop)
    (InAct : B → R → Prop) (w : W)
    (hPow : IntellectualExerciserHasPowerAt a hasCausalPower w)
    (hAct : ActivePowerOnlyInsofarAsInActReading hasCausalPower InAct w) :
    IntellectualExerciseRequiresAct a InAct := by
  sorry

/-- The exerciser causes something (the inner word); causing only of a being
in act (q.75 a.2 reading). -/
theorem intellectualExerciseRequiresActFromProduction {W B Episode R : Type}
    (o : Ontic W B) (a : OperationAttribution B Episode) (InAct : B → R → Prop) (w : W)
    (hProd : IntellectualExerciseProducesAt o a w)
    (hOp : OperationOnlyOfBeingInActReading o InAct w) :
    IntellectualExerciseRequiresAct a InAct := by
  sorry

/-- The exerciser exists at `w`; every existent at `w` is in act of esse. -/
theorem intellectualExerciseRequiresActFromExistence {W B Episode R : Type}
    (m : Ontic W B) (a : OperationAttribution B Episode) (InAct : B → R → Prop)
    (esse : R) (w : W)
    (hEx : IntellectualExerciserExistsAt m a w)
    (hEsse : ExistingInActAt m InAct esse w) :
    IntellectualExerciseRequiresAct a InAct := by
  sorry

/-! ## Map 3: occurring thought is intellectual exercise -/

/-- Every occurring thought is intellective; bearing an intellective episode is
exercising intellect in it. -/
theorem thoughtIsExerciseFromIntellective {B Episode : Type}
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (Intellective : Episode → Prop) (a : OperationAttribution B Episode)
    (hInt : OccurringThoughtIsIntellective Occurs Intellective)
    (hBear : BearingIntellectiveEpisodeIsExercise Bears Intellective a) :
    BorneThoughtExercisesIntellect Occurs Bears a := by
  sorry

/-- The bearer opines the borne thought's content; a bearer opining the content
of its episode exercises intellect in it. -/
theorem thoughtIsExerciseFromOpining {B Episode : Type}
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (Opines : B → Prop → Prop) (content : Episode → Prop)
    (a : OperationAttribution B Episode)
    (hOpin : BorneThoughtIsOpining Occurs Bears Opines content)
    (hJudge : OpiningBorneContentIsIntellectualExercise Bears Opines content a) :
    BorneThoughtExercisesIntellect Occurs Bears a := by
  sorry

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
  sorry

/-- Occurring episodes occur at `w`; bearers exist where their episodes occur. -/
theorem bearerExistsFromWorldIndexedOccurrence {W B Episode : Type}
    (m : Ontic W B) (Occurs : Episode → Prop) (OccursAt : W → Episode → Prop)
    (Bears : B → Episode → Prop) (w : W)
    (hAt : OccurringThoughtOccursAt OccursAt Occurs w)
    (hWhere : BearerExistsWhereEpisodeOccurs m OccursAt Bears) :
    EveryBearerExistsAt m Occurs Bears w := by
  sorry

/-! ## Map 5: the bearer principle -/

/-- Every occurring thought is a modification; no modification without a bearer. -/
theorem everyThoughtHasSubjectFromModification {S Episode : Type}
    (Occurs : Episode → Prop) (Bears : S → Episode → Prop)
    (Modification : Episode → Prop)
    (hMod : OccurringThoughtIsModification Occurs Modification)
    (hNo : NoModificationWithoutBearer Modification Bears) :
    EveryThoughtHasSubject Occurs Bears := by
  sorry

/-- Every occurring thought is an operation; every operation has an agent; the
agent of an episode bears it. -/
theorem everyThoughtHasSubjectFromAgency {S Episode : Type}
    (Occurs : Episode → Prop) (Bears : S → Episode → Prop)
    (IsOperation : Episode → Prop) (AgentOf : S → Episode → Prop)
    (hOper : OccurringThoughtIsOperation Occurs IsOperation)
    (hAgent : EveryOperationHasAgent IsOperation AgentOf)
    (hBears : AgentOfEpisodeBearsIt AgentOf Bears) :
    EveryThoughtHasSubject Occurs Bears := by
  sorry

/-! ## Controls -/

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

/-- The batch controls: one omission model per premise of each derivation
(excluded middle excepted) and one joint nonvacuity witness. -/
theorem controls : Certificate := by
  sorry

end TruthCore.Results.Causality.Round2ExistenceAct
