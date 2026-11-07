module

public import TruthCore.Logic.CogitoEsse
public import TruthCore.Logic.ExcludedMiddle
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.OperationFollowsBeing

/-!
# Round 2: existence, act and the Cogito bearer (exploration maps)

Open analyst premises for derivations of five underived root-path statements:
`ExistingInActAt` (`STMT-EXISTING-IN-ACT-AT`),
`IntellectualExerciseRequiresAct` (`STMT-INTELLECTUAL-EXERCISE-REQUIRES-ACT`),
`BorneThoughtExercisesIntellect` (`STMT-COGITO-THOUGHT-IS-INTELLECTUAL-EXERCISE`),
`EveryBearerExistsAt` (`STMT-COGITO-BEARER-EXISTS-AT-WORLD`) and
`EveryThoughtHasSubject` (`STMT-COGITO-EVERY-THOUGHT-HAS-SUBJECT`).
Maps: `explorations/existing-in-act-at.toml` and its four siblings.

Every definition below is an OPEN analyst formulation with attribution
deferred. New predicate parameters (`MerelyPossible`, `Operates`,
`Intellective`, `OccursAt`, `Modification`, `IsOperation`, `AgentOf`) are
unconstrained except by the premises that use them; their intended senses are
recorded in the linked `DEF-` records. `InAct`, `esse`, `Ontic`,
`OperationAttribution`, `Occurs` and `Bears` keep the meanings of the reused
vocabulary.
-/

@[expose] public section

namespace TruthCore.Causality.Round2ExistenceAct

open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect (OperationAttribution)

/-! ## Map 1: the esse contract -/

/-- OPEN: at the selected world every existent is in act in some respect (to be
is to be actual in some way). Says nothing about which respect. -/
def ExistentInActInSomeRespectAt {W B R : Type} (m : Ontic W B)
    (InAct : B → R → Prop) (w : W) : Prop :=
  ∀ x, m.ExistsAt w x → ∃ r, InAct x r

/-- OPEN Eleatic principle at the selected world: every existent has causal
power (`DEF-POWER-CAPACITY-READING`: a capacity, not a present exercise).
Rejected by Platonists about causally inert abstracta and by epiphenomenalists. -/
def EveryExistentHasCausalPowerAt {W B : Type} (m : Ontic W B)
    (hasCausalPower : W → B → Prop) (w : W) : Prop :=
  ∀ x, m.ExistsAt w x → hasCausalPower w x

/-- OPEN: whatever is not in act of esse is merely possible (in potency to
being only, `DEF-MERELY-POSSIBLE-CANDIDATE`). -/
def LackingEsseIsMerelyPossible {B R : Type} (InAct : B → R → Prop) (esse : R)
    (MerelyPossible : B → Prop) : Prop :=
  ∀ x, ¬ InAct x esse → MerelyPossible x

/-- OPEN: nothing merely possible exists at the selected world. -/
def MerelyPossibleNotExistentAt {W B : Type} (m : Ontic W B)
    (MerelyPossible : B → Prop) (w : W) : Prop :=
  ∀ x, MerelyPossible x → ¬ m.ExistsAt w x

/-! ## Map 2: intellectual exercise requires act -/

/-- OPEN: whoever is attributed an intellectual exercise operates
(`DEF-OPERATING-AGENT`). -/
def IntellectualExerciseIsOperating {B Episode : Type}
    (a : OperationAttribution B Episode) (Operates : B → Prop) : Prop :=
  ∀ b e, a.IntellectualExercise b e → Operates b

/-- OPEN generic operari sequitur esse: whatever operates is in act in some
respect. The q.75 a.2 reading `OperationOnlyOfBeingInActReading` states this
only of causing another; this version is about operating as such, including
immanent operation. -/
def OperatingOnlyOfBeingInAct {B R : Type} (Operates : B → Prop)
    (InAct : B → R → Prop) : Prop :=
  ∀ b, Operates b → ∃ r, InAct b r

/-- OPEN: whoever is attributed an intellectual exercise has causal (active)
power at the selected world. -/
def IntellectualExerciserHasPowerAt {W B Episode : Type}
    (a : OperationAttribution B Episode) (hasCausalPower : W → B → Prop) (w : W) : Prop :=
  ∀ b e, a.IntellectualExercise b e → hasCausalPower w b

/-- OPEN and contested: whoever exercises intellect causes something at the
selected world (the inner word or concept). Aquinas calls understanding an
immanent action, which this premise treats as also a causing. -/
def IntellectualExerciseProducesAt {W B Episode : Type} (o : Ontic W B)
    (a : OperationAttribution B Episode) (w : W) : Prop :=
  ∀ b e, a.IntellectualExercise b e → ∃ y, o.Causes w b y

/-- OPEN: whoever is attributed an intellectual exercise exists at the
selected world. -/
def IntellectualExerciserExistsAt {W B Episode : Type} (m : Ontic W B)
    (a : OperationAttribution B Episode) (w : W) : Prop :=
  ∀ b e, a.IntellectualExercise b e → m.ExistsAt w b

/-! ## Map 3: occurring thought is intellectual exercise -/

/-- OPEN: every occurring thought episode is intellective
(`DEF-INTELLECTIVE-EPISODE`: an act of understanding or judging, not a mere
sensation or feeling). Denied on Descartes's broad reading of cogitatio. -/
def OccurringThoughtIsIntellective {Episode : Type} (Occurs : Episode → Prop)
    (Intellective : Episode → Prop) : Prop :=
  ∀ e, Occurs e → Intellective e

/-- OPEN: whoever bears an intellective episode is attributed it as an
intellectual exercise. -/
def BearingIntellectiveEpisodeIsExercise {B Episode : Type}
    (Bears : B → Episode → Prop) (Intellective : Episode → Prop)
    (a : OperationAttribution B Episode) : Prop :=
  ∀ b e, Intellective e → Bears b e → a.IntellectualExercise b e

/-- OPEN: whoever bears an episode and opines its content exercises intellect
in it (judging is an act of intellect). `DEF-OPINING` includes phantasia, so
anyone who places imagination in sense contests this premise. -/
def OpiningBorneContentIsIntellectualExercise {B Episode : Type}
    (Bears : B → Episode → Prop) (Opines : B → Prop → Prop)
    (content : Episode → Prop) (a : OperationAttribution B Episode) : Prop :=
  ∀ b e, Bears b e → Opines b (content e) → a.IntellectualExercise b e

/-! ## Map 4: the bearer exists at the selected world -/

/-- OPEN converse of `ExistingInActAt`: whatever is in act of esse exists at the
selected world. `InAct` is not world-indexed, so this reads esse relative to the
selected world; `TruthCore.Logic.CogitoEsse` does not assert it. -/
def ActOfEsseSufficesForExistenceAt {W B R : Type} (m : Ontic W B)
    (InAct : B → R → Prop) (esse : R) (w : W) : Prop :=
  ∀ x, InAct x esse → m.ExistsAt w x

/-- OPEN: every occurring episode occurs at the selected world
(`DEF-EPISODE-OCCURS-AT`). -/
def OccurringThoughtOccursAt {W Episode : Type} (OccursAt : W → Episode → Prop)
    (Occurs : Episode → Prop) (w : W) : Prop :=
  ∀ e, Occurs e → OccursAt w e

/-- OPEN: at any world, whoever bears an episode occurring there exists there. -/
def BearerExistsWhereEpisodeOccurs {W B Episode : Type} (m : Ontic W B)
    (OccursAt : W → Episode → Prop) (Bears : B → Episode → Prop) : Prop :=
  ∀ v b e, OccursAt v e → Bears b e → m.ExistsAt v b

/-! ## Map 5: the bearer principle -/

/-- OPEN: every occurring thought episode is a modification (mode or accident,
`DEF-EPISODE-MODIFICATION`), not a self-standing thing. -/
def OccurringThoughtIsModification {Episode : Type} (Occurs : Episode → Prop)
    (Modification : Episode → Prop) : Prop :=
  ∀ e, Occurs e → Modification e

/-- OPEN: every modification is borne by something (nothingness has no
properties). Denied by bundle theories. -/
def NoModificationWithoutBearer {S Episode : Type} (Modification : Episode → Prop)
    (Bears : S → Episode → Prop) : Prop :=
  ∀ e, Modification e → ∃ s, Bears s e

/-- OPEN: every occurring thought episode is an operation (an activity, not a
mere event). -/
def OccurringThoughtIsOperation {Episode : Type} (Occurs : Episode → Prop)
    (IsOperation : Episode → Prop) : Prop :=
  ∀ e, Occurs e → IsOperation e

/-- OPEN: every operation has an agent (`DEF-EPISODE-AGENT`). -/
def EveryOperationHasAgent {S Episode : Type} (IsOperation : Episode → Prop)
    (AgentOf : S → Episode → Prop) : Prop :=
  ∀ e, IsOperation e → ∃ s, AgentOf s e

/-- OPEN: the agent of an episode bears it. -/
def AgentOfEpisodeBearsIt {S Episode : Type} (AgentOf Bears : S → Episode → Prop) : Prop :=
  ∀ s e, AgentOf s e → Bears s e

/-! ## Controls -/

namespace Control

open TruthCore.Causality.ExistenceActuality
open TruthCore.Logic.CogitoEsse
open TruthCore.Logic.CogitoConcrete
open TruthCore.Logic.CogitoSubject
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.OperationFollowsBeing

/-- One-element carriers are `Unit`; these instances decide its quantifiers
without axioms (the `Fin` instances use `propext`). -/
instance unitForallDecidable (P : Unit → Prop) [h : Decidable (P ())] : Decidable (∀ x, P x) :=
  match h with
  | isTrue hp => isTrue (fun _ => hp)
  | isFalse hn => isFalse (fun hall => hn (hall ()))

instance unitExistsDecidable (P : Unit → Prop) [h : Decidable (P ())] : Decidable (∃ x, P x) :=
  match h with
  | isTrue hp => isTrue ⟨(), hp⟩
  | isFalse hn => isFalse (fun ⟨_, hx⟩ => hn hx)

/-- A one-world, one-candidate signature with the given existence and causing
extensions. -/
abbrev ont (ex cs : Prop) : Ontic Unit Unit where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => ex
  Causes := fun _ _ _ => cs

/-- A one-principle, one-operation attribution with the given exercise extension. -/
abbrev att (ie : Prop) : OperationAttribution Unit Unit where
  IntellectualExercise := fun _ _ => ie
  BodyShares := fun _ => False
  InheresAsAccidentOrMaterialForm := fun _ => False
  CompleteInSpecies := fun _ => False

/-- Two respects: `esse = true`; things are in act only in the other respect. -/
abbrev notEsse : Unit → Bool → Prop := fun _ r => r = false

/-! ### Map 1 -/

/-- `existingInActAtFromSomeAct`, omit `hSome`: something exists, nothing is in act. -/
def omitSomeAct : Prop :=
  ¬ ExistentInActInSomeRespectAt (ont True False) (fun _ (_ : Unit) => False) () ∧
    ActualityOnlyInsofarAsBeingReading (fun (_ : Unit) (_ : Unit) => False) () ∧
    ¬ ExistingInActAt (ont True False) (fun _ (_ : Unit) => False) () ()

/-- `existingInActAtFromSomeAct`, omit `hOnly`: the existent is in act only in
a respect other than esse. -/
def omitActualityOnly1 : Prop :=
  ExistentInActInSomeRespectAt (ont True False) notEsse () ∧
    ¬ ActualityOnlyInsofarAsBeingReading notEsse true ∧
    ¬ ExistingInActAt (ont True False) notEsse true ()

/-- `existingInActAtFromEleaticPower`, omit `hPow`: the existent has no power. -/
def omitEleatic : Prop :=
  ¬ EveryExistentHasCausalPowerAt (ont True False) (fun _ _ => False) () ∧
    ActivePowerOnlyInsofarAsInActReading (fun (_ : Unit) (_ : Unit) => False)
      (fun _ (_ : Unit) => False) () ∧
    ActualityOnlyInsofarAsBeingReading (fun (_ : Unit) (_ : Unit) => False) () ∧
    ¬ ExistingInActAt (ont True False) (fun _ (_ : Unit) => False) () ()

/-- `existingInActAtFromEleaticPower`, omit `hAct`: power without act. -/
def omitActivePower1 : Prop :=
  EveryExistentHasCausalPowerAt (ont True False) (fun _ _ => True) () ∧
    ¬ ActivePowerOnlyInsofarAsInActReading (fun (_ : Unit) (_ : Unit) => True)
      (fun _ (_ : Unit) => False) () ∧
    ActualityOnlyInsofarAsBeingReading (fun (_ : Unit) (_ : Unit) => False) () ∧
    ¬ ExistingInActAt (ont True False) (fun _ (_ : Unit) => False) () ()

/-- `existingInActAtFromEleaticPower`, omit `hOnly`. -/
def omitActualityOnly2 : Prop :=
  EveryExistentHasCausalPowerAt (ont True False) (fun _ _ => True) () ∧
    ActivePowerOnlyInsofarAsInActReading (fun (_ : Unit) (_ : Unit) => True) notEsse () ∧
    ¬ ActualityOnlyInsofarAsBeingReading notEsse true ∧
    ¬ ExistingInActAt (ont True False) notEsse true ()

/-- `existingInActAtFromMerePossibility`, omit `hLack` (excluded middle holds
classically in every model and is not restated). -/
def omitLackingEsse : Prop :=
  ¬ LackingEsseIsMerelyPossible (fun (_ : Unit) (_ : Unit) => False) () (fun _ => False) ∧
    MerelyPossibleNotExistentAt (ont True False) (fun _ => False) () ∧
    ¬ ExistingInActAt (ont True False) (fun _ (_ : Unit) => False) () ()

/-- `existingInActAtFromMerePossibility`, omit `hMP`: a merely possible existent. -/
def omitMerelyPossible : Prop :=
  LackingEsseIsMerelyPossible (fun (_ : Unit) (_ : Unit) => False) () (fun _ => True) ∧
    ¬ MerelyPossibleNotExistentAt (ont True False) (fun _ => True) () ∧
    ¬ ExistingInActAt (ont True False) (fun _ (_ : Unit) => False) () ()

/-- `existentInActFromEleaticPower`, omit `hPow`. -/
def omitEleatic2 : Prop :=
  ¬ EveryExistentHasCausalPowerAt (ont True False) (fun _ _ => False) () ∧
    ActivePowerOnlyInsofarAsInActReading (fun (_ : Unit) (_ : Unit) => False)
      (fun _ (_ : Unit) => False) () ∧
    ¬ ExistentInActInSomeRespectAt (ont True False) (fun _ (_ : Unit) => False) ()

/-- `existentInActFromEleaticPower`, omit `hAct`. -/
def omitActivePower2 : Prop :=
  EveryExistentHasCausalPowerAt (ont True False) (fun _ _ => True) () ∧
    ¬ ActivePowerOnlyInsofarAsInActReading (fun (_ : Unit) (_ : Unit) => True)
      (fun _ (_ : Unit) => False) () ∧
    ¬ ExistentInActInSomeRespectAt (ont True False) (fun _ (_ : Unit) => False) ()

/-! ### Map 2 -/

/-- `intellectualExerciseRequiresActFromOperating`, omit `hOp`. -/
def omitExerciseIsOperating : Prop :=
  ¬ IntellectualExerciseIsOperating (att True) (fun _ => False) ∧
    OperatingOnlyOfBeingInAct (fun (_ : Unit) => False) (fun _ (_ : Unit) => False) ∧
    ¬ IntellectualExerciseRequiresAct (att True) (fun _ (_ : Unit) => False)

/-- `intellectualExerciseRequiresActFromOperating`, omit `hOnly`. -/
def omitOperatingOnlyInAct : Prop :=
  IntellectualExerciseIsOperating (att True) (fun _ => True) ∧
    ¬ OperatingOnlyOfBeingInAct (fun (_ : Unit) => True) (fun _ (_ : Unit) => False) ∧
    ¬ IntellectualExerciseRequiresAct (att True) (fun _ (_ : Unit) => False)

/-- `intellectualExerciseRequiresActFromActivePower`, omit `hPow`. -/
def omitExerciserPower : Prop :=
  ¬ IntellectualExerciserHasPowerAt (att True) (fun _ _ => False) () ∧
    ActivePowerOnlyInsofarAsInActReading (fun (_ : Unit) (_ : Unit) => False)
      (fun _ (_ : Unit) => False) () ∧
    ¬ IntellectualExerciseRequiresAct (att True) (fun _ (_ : Unit) => False)

/-- `intellectualExerciseRequiresActFromActivePower`, omit `hAct`. -/
def omitActivePower3 : Prop :=
  IntellectualExerciserHasPowerAt (att True) (fun _ _ => True) () ∧
    ¬ ActivePowerOnlyInsofarAsInActReading (fun (_ : Unit) (_ : Unit) => True)
      (fun _ (_ : Unit) => False) () ∧
    ¬ IntellectualExerciseRequiresAct (att True) (fun _ (_ : Unit) => False)

/-- `intellectualExerciseRequiresActFromProduction`, omit `hProd`. -/
def omitProduces : Prop :=
  ¬ IntellectualExerciseProducesAt (ont True False) (att True) () ∧
    OperationOnlyOfBeingInActReading (ont True False) (fun _ (_ : Unit) => False) () ∧
    ¬ IntellectualExerciseRequiresAct (att True) (fun _ (_ : Unit) => False)

/-- `intellectualExerciseRequiresActFromProduction`, omit `hOp`. -/
def omitOperationOnlyInAct : Prop :=
  IntellectualExerciseProducesAt (ont True True) (att True) () ∧
    ¬ OperationOnlyOfBeingInActReading (ont True True) (fun _ (_ : Unit) => False) () ∧
    ¬ IntellectualExerciseRequiresAct (att True) (fun _ (_ : Unit) => False)

/-- `intellectualExerciseRequiresActFromExistence`, omit `hEx`. -/
def omitExerciserExists : Prop :=
  ¬ IntellectualExerciserExistsAt (ont False False) (att True) () ∧
    ExistingInActAt (ont False False) (fun _ (_ : Unit) => False) () () ∧
    ¬ IntellectualExerciseRequiresAct (att True) (fun _ (_ : Unit) => False)

/-- `intellectualExerciseRequiresActFromExistence`, omit `hEsse`. -/
def omitExistingInAct : Prop :=
  IntellectualExerciserExistsAt (ont True False) (att True) () ∧
    ¬ ExistingInActAt (ont True False) (fun _ (_ : Unit) => False) () () ∧
    ¬ IntellectualExerciseRequiresAct (att True) (fun _ (_ : Unit) => False)

/-! ### Map 3 -/

/-- `thoughtIsExerciseFromIntellective`, omit `hInt`. -/
def omitIntellective : Prop :=
  ¬ OccurringThoughtIsIntellective (fun (_ : Unit) => True) (fun _ => False) ∧
    BearingIntellectiveEpisodeIsExercise (fun (_ _ : Unit) => True) (fun _ => False) (att False) ∧
    ¬ BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att False)

/-- `thoughtIsExerciseFromIntellective`, omit `hBear`. -/
def omitBearingIntellective : Prop :=
  OccurringThoughtIsIntellective (fun (_ : Unit) => True) (fun _ => True) ∧
    ¬ BearingIntellectiveEpisodeIsExercise (fun (_ _ : Unit) => True) (fun _ => True) (att False) ∧
    ¬ BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att False)

/-- `thoughtIsExerciseFromOpining`, omit `hOpin`. -/
def omitBorneOpining : Prop :=
  ¬ BorneThoughtIsOpining (fun (_ : Unit) => True) (fun (_ _ : Unit) => True)
      (fun _ _ => False) (fun _ => True) ∧
    OpiningBorneContentIsIntellectualExercise (fun _ _ => True) (fun _ _ => False)
      (fun _ => True) (att False) ∧
    ¬ BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att False)

/-- `thoughtIsExerciseFromOpining`, omit `hJudge`. -/
def omitOpiningIsExercise : Prop :=
  BorneThoughtIsOpining (fun (_ : Unit) => True) (fun (_ _ : Unit) => True)
      (fun _ _ => True) (fun _ => True) ∧
    ¬ OpiningBorneContentIsIntellectualExercise (fun _ _ => True) (fun _ _ => True)
      (fun _ => True) (att False) ∧
    ¬ BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att False)

/-! ### Map 4 -/

/-- `bearerExistsFromOperationAndEsse`, omit `hThought`. -/
def omitThoughtIsExercise : Prop :=
  ¬ BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att False) ∧
    IntellectualExerciseRequiresAct (att False) (fun _ (_ : Unit) => False) ∧
    ActualityOnlyInsofarAsBeingReading (fun (_ : Unit) (_ : Unit) => False) () ∧
    ActOfEsseSufficesForExistenceAt (ont False False) (fun _ (_ : Unit) => False) () () ∧
    ¬ EveryBearerExistsAt (ont False False) (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) ()

/-- `bearerExistsFromOperationAndEsse`, omit `hReq`. -/
def omitExerciseRequiresAct : Prop :=
  BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att True) ∧
    ¬ IntellectualExerciseRequiresAct (att True) (fun _ (_ : Unit) => False) ∧
    ActualityOnlyInsofarAsBeingReading (fun (_ : Unit) (_ : Unit) => False) () ∧
    ActOfEsseSufficesForExistenceAt (ont False False) (fun _ (_ : Unit) => False) () () ∧
    ¬ EveryBearerExistsAt (ont False False) (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) ()

/-- `bearerExistsFromOperationAndEsse`, omit `hOnly`: the bearer is in act only
in a respect other than esse. -/
def omitActualityOnly3 : Prop :=
  BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att True) ∧
    IntellectualExerciseRequiresAct (att True) notEsse ∧
    ¬ ActualityOnlyInsofarAsBeingReading notEsse true ∧
    ActOfEsseSufficesForExistenceAt (ont False False) notEsse true () ∧
    ¬ EveryBearerExistsAt (ont False False) (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) ()

/-- `bearerExistsFromOperationAndEsse`, omit `hSuff`: a bearer in act of esse
that does not exist at the selected world. -/
def omitEsseSuffices : Prop :=
  BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att True) ∧
    IntellectualExerciseRequiresAct (att True) (fun _ (_ : Unit) => True) ∧
    ActualityOnlyInsofarAsBeingReading (fun (_ : Unit) (_ : Unit) => True) () ∧
    ¬ ActOfEsseSufficesForExistenceAt (ont False False) (fun _ (_ : Unit) => True) () () ∧
    ¬ EveryBearerExistsAt (ont False False) (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) ()

/-- `bearerExistsFromWorldIndexedOccurrence`, omit `hAt`. -/
def omitOccursAt : Prop :=
  ¬ OccurringThoughtOccursAt (fun _ _ => False) (fun (_ : Unit) => True) () ∧
    BearerExistsWhereEpisodeOccurs (ont False False) (fun (_ _ : Unit) => False) (fun _ _ => True) ∧
    ¬ EveryBearerExistsAt (ont False False) (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) ()

/-- `bearerExistsFromWorldIndexedOccurrence`, omit `hWhere`. -/
def omitBearerWhere : Prop :=
  OccurringThoughtOccursAt (fun _ _ => True) (fun (_ : Unit) => True) () ∧
    ¬ BearerExistsWhereEpisodeOccurs (ont False False) (fun (_ _ : Unit) => True) (fun _ _ => True) ∧
    ¬ EveryBearerExistsAt (ont False False) (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) ()

/-! ### Map 5 -/

/-- `everyThoughtHasSubjectFromModification`, omit `hMod`. -/
def omitModification : Prop :=
  ¬ OccurringThoughtIsModification (fun (_ : Unit) => True) (fun _ => False) ∧
    NoModificationWithoutBearer (fun _ => False) (fun (_ _ : Unit) => False) ∧
    ¬ EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => False)

/-- `everyThoughtHasSubjectFromModification`, omit `hNo`: a bearerless mode. -/
def omitNoModWithoutBearer : Prop :=
  OccurringThoughtIsModification (fun (_ : Unit) => True) (fun _ => True) ∧
    ¬ NoModificationWithoutBearer (fun _ => True) (fun (_ _ : Unit) => False) ∧
    ¬ EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => False)

/-- `everyThoughtHasSubjectFromAgency`, omit `hOper`. -/
def omitIsOperation : Prop :=
  ¬ OccurringThoughtIsOperation (fun (_ : Unit) => True) (fun _ => False) ∧
    EveryOperationHasAgent (fun _ => False) (fun (_ _ : Unit) => False) ∧
    AgentOfEpisodeBearsIt (fun (_ _ : Unit) => False) (fun _ _ => False) ∧
    ¬ EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => False)

/-- `everyThoughtHasSubjectFromAgency`, omit `hAgent`: an agentless operation. -/
def omitHasAgent : Prop :=
  OccurringThoughtIsOperation (fun (_ : Unit) => True) (fun _ => True) ∧
    ¬ EveryOperationHasAgent (fun _ => True) (fun (_ _ : Unit) => False) ∧
    AgentOfEpisodeBearsIt (fun (_ _ : Unit) => False) (fun _ _ => False) ∧
    ¬ EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => False)

/-- `everyThoughtHasSubjectFromAgency`, omit `hBears`: an agent that does not
bear its episode. -/
def omitAgentBears : Prop :=
  OccurringThoughtIsOperation (fun (_ : Unit) => True) (fun _ => True) ∧
    EveryOperationHasAgent (fun _ => True) (fun (_ _ : Unit) => True) ∧
    ¬ AgentOfEpisodeBearsIt (fun (_ _ : Unit) => True) (fun _ _ => False) ∧
    ¬ EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => False)

/-! ### Joint nonvacuity witness -/

/-- One joint model with a thought that occurs, a bearer that exists, exercises
intellect, opines, causes and is in act of esse, in which every premise (other
than excluded middle) and every conclusion of the batch holds. -/
def witness : Prop :=
  -- map 1
  ExistentInActInSomeRespectAt (ont True True) (fun _ (_ : Unit) => True) () ∧
    ActualityOnlyInsofarAsBeingReading (fun (_ : Unit) (_ : Unit) => True) () ∧
    EveryExistentHasCausalPowerAt (ont True True) (fun _ _ => True) () ∧
    ActivePowerOnlyInsofarAsInActReading (fun (_ : Unit) (_ : Unit) => True)
      (fun _ (_ : Unit) => True) () ∧
    LackingEsseIsMerelyPossible (fun (_ : Unit) (_ : Unit) => True) () (fun _ => False) ∧
    MerelyPossibleNotExistentAt (ont True True) (fun _ => False) () ∧
    ExistingInActAt (ont True True) (fun _ (_ : Unit) => True) () () ∧
  -- map 2
    IntellectualExerciseIsOperating (att True) (fun _ => True) ∧
    OperatingOnlyOfBeingInAct (fun (_ : Unit) => True) (fun _ (_ : Unit) => True) ∧
    IntellectualExerciserHasPowerAt (att True) (fun _ _ => True) () ∧
    IntellectualExerciseProducesAt (ont True True) (att True) () ∧
    OperationOnlyOfBeingInActReading (ont True True) (fun _ (_ : Unit) => True) () ∧
    IntellectualExerciserExistsAt (ont True True) (att True) () ∧
    IntellectualExerciseRequiresAct (att True) (fun _ (_ : Unit) => True) ∧
  -- map 3
    OccurringThoughtIsIntellective (fun (_ : Unit) => True) (fun _ => True) ∧
    BearingIntellectiveEpisodeIsExercise (fun (_ _ : Unit) => True) (fun _ => True) (att True) ∧
    BorneThoughtIsOpining (fun (_ : Unit) => True) (fun (_ _ : Unit) => True)
      (fun _ _ => True) (fun _ => True) ∧
    OpiningBorneContentIsIntellectualExercise (fun _ _ => True) (fun _ _ => True)
      (fun _ => True) (att True) ∧
    BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att True) ∧
  -- map 4
    ActOfEsseSufficesForExistenceAt (ont True True) (fun _ (_ : Unit) => True) () () ∧
    OccurringThoughtOccursAt (fun _ _ => True) (fun (_ : Unit) => True) () ∧
    BearerExistsWhereEpisodeOccurs (ont True True) (fun (_ _ : Unit) => True) (fun _ _ => True) ∧
    EveryBearerExistsAt (ont True True) (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) () ∧
  -- map 5
    OccurringThoughtIsModification (fun (_ : Unit) => True) (fun _ => True) ∧
    NoModificationWithoutBearer (fun _ => True) (fun (_ _ : Unit) => True) ∧
    OccurringThoughtIsOperation (fun (_ : Unit) => True) (fun _ => True) ∧
    EveryOperationHasAgent (fun _ => True) (fun (_ _ : Unit) => True) ∧
    AgentOfEpisodeBearsIt (fun (_ _ : Unit) => True) (fun _ _ => True) ∧
    EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) ∧
    TruthCore.Logic.CogitoSubject.ThoughtOccurs (fun (_ : Unit) => True)

/-- The batch controls: one omission model per premise of each derivation
(excluded middle excepted: it is logical and holds classically in every model)
and one joint nonvacuity witness. Satisfiability and omission only; no model is
claimed to describe reality. -/
def Certificate : Prop :=
  omitSomeAct ∧ omitActualityOnly1 ∧ omitEleatic ∧ omitActivePower1 ∧
    omitActualityOnly2 ∧ omitLackingEsse ∧ omitMerelyPossible ∧ omitEleatic2 ∧
    omitActivePower2 ∧
    omitExerciseIsOperating ∧ omitOperatingOnlyInAct ∧ omitExerciserPower ∧
    omitActivePower3 ∧ omitProduces ∧ omitOperationOnlyInAct ∧ omitExerciserExists ∧
    omitExistingInAct ∧
    omitIntellective ∧ omitBearingIntellective ∧ omitBorneOpining ∧ omitOpiningIsExercise ∧
    omitThoughtIsExercise ∧ omitExerciseRequiresAct ∧ omitActualityOnly3 ∧ omitEsseSuffices ∧
    omitOccursAt ∧ omitBearerWhere ∧
    omitModification ∧ omitNoModWithoutBearer ∧ omitIsOperation ∧ omitHasAgent ∧
    omitAgentBears ∧ witness

end Control

end TruthCore.Causality.Round2ExistenceAct
