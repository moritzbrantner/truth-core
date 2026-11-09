module
public import TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesAll.Solution
@[expose] public section
namespace TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic
/-- Only actual-perfection bearers are compared with a God candidate.
The second conjunct is stability of that candidate's represented esse/essence
identity, not a global decision procedure or an attribute assumption. -/
def LocalLogic {Being Respect Principle : Type} (IsGod : Being → Prop)
    (InAct : Being → Respect → Prop) (esseOf essenceOf : Being → Principle) : Prop :=
  ∀ g, IsGod g →
    (∀ x r, InAct x r → x = g ∨ x ≠ g) ∧
    (¬¬ (esseOf g = essenceOf g) → esseOf g = essenceOf g)

def signature (attributes : Prop) : TruthCore.Case.Catholicism.Signature where
  Being := Unit
  IsGod := fun _ => True
  HasClassicalAttributes := fun _ => attributes
  RevealsRecognizably := fun _ => False
  jesus := ()
  ClaimedDivineAuthority := fun _ => False
  RoseFromTheDead := fun _ => False
  Society := Unit
  catholicChurch := ()
  Founded := fun _ _ => False
  VisibleWithAuthority := fun _ => False
  FoundedAsTeachingAuthority := fun _ _ => False
  DefinitivelyProposesAsRevealed := fun _ _ => False
  creedOneGodFatherAlmightyCreator := False
  creedOneLordJesusChristOnlyBegottenConsubstantial := False
  creedIncarnateOfSpiritAndVirginMary := False
  creedCrucifiedUnderPilateSufferedBuried := False
  creedRoseOnTheThirdDay := False
  creedAscendedSeatedAtRightHand := False
  creedWillComeToJudgeKingdomWithoutEnd := False
  creedHolySpiritLordGiverOfLife := False
  creedOneHolyCatholicApostolicChurch := False
  creedOneBaptismForForgiveness := False
  creedResurrectionOfTheDead := False
  creedLifeOfTheWorldToCome := False

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism

/-- All seventeen other nonlogical inputs and the local fragment hold in an inhabited interpretation. -/
def ModelBackground (attributes : Prop) : Prop :=
  let σ := signature attributes
  let InPotency : Unit → Unit → Prop := fun _ _ => False
  let InAct : Unit → Unit → Prop := fun _ _ => True
  let GoodIn := InAct
  let MoreIn : Unit → Unit → Unit → Prop := fun _ _ _ => False
  let CausesIn : Unit → Unit → Unit → Prop := fun _ _ _ => False
  let esse := ()
  let ComponentOf : Unit → Unit → Prop := fun _ _ => False
  let PriorSimply := ComponentOf
  let Composite : Unit → Prop := fun _ => False
  let ComposedOfMatterAndForm := Composite
  let Infinite : Unit → Prop := fun _ => True
  let Eternal := Infinite
  let HasIntellect := Infinite
  let HasWill := Infinite
  let essenceOf : Unit → Unit := fun _ => ()
  let esseOf := essenceOf
  GodIsMaximalInBeing σ.IsGod InAct MoreIn esse ∧
  MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn ∧
  CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn ∧
  TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic.LocalLogic σ.IsGod InAct esseOf essenceOf ∧
  CompositeHasAUnitingCauseReading Composite CausesIn esse ∧
  ActualityOnlyInsofarAsBeingReading InAct esse ∧
  PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse ∧
  GoodnessIsActualityReading GoodIn InAct ∧
  CauseOfBeingCausesEveryPerfection InAct CausesIn esse ∧
  MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply ∧
  ActSimplyPriorToPotencyReading InAct InPotency PriorSimply ∧
  NotActAndPotencyInSameRespectReading InAct InPotency ∧
  MatterFormAndEsseEssenceAreCompositionsReading ComposedOfMatterAndForm Composite
      essenceOf esseOf ∧
  SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite ∧
  ImmutableIsEternalReading InPotency Eternal ∧
  NoComponentIsFirstBeingReading ComponentOf PriorSimply ∧
  ImmaterialIsIntellectualReading ComposedOfMatterAndForm HasIntellect
      ComponentOf ∧
  WillFollowsIntellectReading HasIntellect HasWill

/-- The primitive attributes field is independent of the retained background without sufficiency. -/
def Controls : Prop := ModelBackground True ∧ ModelBackground False ∧
  (signature True).IsGod () ∧ (signature True).HasClassicalAttributes () ∧
  (signature False).IsGod () ∧ ¬ (signature False).HasClassicalAttributes ()

end TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic
