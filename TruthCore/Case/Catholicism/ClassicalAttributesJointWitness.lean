module

public import TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesAll.Solution

@[expose] public section
namespace TruthCore.Case.Catholicism.ClassicalAttributesJointWitness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics

/-- Two formal individuals and respects, not a claim about metaphysical possibility. -/
abbrev Being := Bool
abbrev Respect := Bool
abbrev Principle := Bool
def InAct (x : Being) (r : Respect) : Prop := x = false ∨ r = false
def InPotency (x : Being) (r : Respect) : Prop := x = true ∧ r = true
def GoodIn := InAct
def MoreIn (_ : Respect) (x y : Being) : Prop := x = false ∧ y = true
def CausesIn (x y : Being) (_ : Respect) : Prop := x = false ∧ y = true
def ComponentOf (x y : Being) : Prop := x = true ∧ y = true
def PriorSimply (x y : Being) : Prop := x = false ∧ y = true
def Composite (x : Being) : Prop := x = true
def ComposedOfMatterAndForm := Composite
def Infinite (x : Being) : Prop := x = false
def Eternal := Infinite
def HasIntellect := Infinite
def HasWill := Infinite
def essenceOf (x : Being) : Principle := x
def esseOf (_ : Being) : Principle := false
def esse : Respect := false

def σ : Signature where
  Being := Being
  IsGod := fun x => x = false
  HasClassicalAttributes := fun x => x = false
  RevealsRecognizably := fun _ => False
  jesus := true
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

/-- Original assembly hypothesis `hSuffice`, at this one assignment. -/
def Premise0 : Prop :=
  ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect InAct)
      (IsSupremelyGood InAct GoodIn CausesIn esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill

/-- Original assembly hypothesis `hMaximal`, at this one assignment. -/
def Premise1 : Prop :=
  GodIsMaximalInBeing σ.IsGod InAct MoreIn esse

/-- Original assembly hypothesis `hGenus`, at this one assignment. -/
def Premise2 : Prop :=
  MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn

/-- Original assembly hypothesis `hCauseMore`, at this one assignment. -/
def Premise3 : Prop :=
  CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn

/-- Original assembly hypothesis `hEM`, at this one assignment. -/
def Premise4 : Prop :=
  TruthCore.Logic.ExcludedMiddle

/-- Original assembly hypothesis `hUniting`, at this one assignment. -/
def Premise5 : Prop :=
  CompositeHasAUnitingCauseReading Composite CausesIn esse

/-- Original assembly hypothesis `hBeing`, at this one assignment. -/
def Premise6 : Prop :=
  ActualityOnlyInsofarAsBeingReading InAct esse

/-- Original assembly hypothesis `hPreexist`, at this one assignment. -/
def Premise7 : Prop :=
  PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse

/-- Original assembly hypothesis `hGoodness`, at this one assignment. -/
def Premise8 : Prop :=
  GoodnessIsActualityReading GoodIn InAct

/-- Original assembly hypothesis `hPerfections`, at this one assignment. -/
def Premise9 : Prop :=
  CauseOfBeingCausesEveryPerfection InAct CausesIn esse

/-- Original assembly hypothesis `hFirstBeing`, at this one assignment. -/
def Premise10 : Prop :=
  MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply

/-- Original assembly hypothesis `hPrior`, at this one assignment. -/
def Premise11 : Prop :=
  ActSimplyPriorToPotencyReading InAct InPotency PriorSimply

/-- Original assembly hypothesis `hNotBoth`, at this one assignment. -/
def Premise12 : Prop :=
  NotActAndPotencyInSameRespectReading InAct InPotency

/-- Original assembly hypothesis `hKinds`, at this one assignment. -/
def Premise13 : Prop :=
  MatterFormAndEsseEssenceAreCompositionsReading ComposedOfMatterAndForm Composite
      essenceOf esseOf

/-- Original assembly hypothesis `hInfinity`, at this one assignment. -/
def Premise14 : Prop :=
  SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite

/-- Original assembly hypothesis `hEternity`, at this one assignment. -/
def Premise15 : Prop :=
  ImmutableIsEternalReading InPotency Eternal

/-- Original assembly hypothesis `hNoComponent`, at this one assignment. -/
def Premise16 : Prop :=
  NoComponentIsFirstBeingReading ComponentOf PriorSimply

/-- Original assembly hypothesis `hImmaterial`, at this one assignment. -/
def Premise17 : Prop :=
  ImmaterialIsIntellectualReading ComposedOfMatterAndForm HasIntellect
      ComponentOf

/-- Original assembly hypothesis `hWillFollows`, at this one assignment. -/
def Premise18 : Prop :=
  WillFollowsIntellectReading HasIntellect HasWill

def AllPremises : Prop :=
  Premise0 ∧
  Premise1 ∧
  Premise2 ∧
  Premise3 ∧
  Premise4 ∧
  Premise5 ∧
  Premise6 ∧
  Premise7 ∧
  Premise8 ∧
  Premise9 ∧
  Premise10 ∧
  Premise11 ∧
  Premise12 ∧
  Premise13 ∧
  Premise14 ∧
  Premise15 ∧
  Premise16 ∧
  Premise17 ∧
  Premise18

def Nonvacuity : Prop :=
  σ.IsGod false ∧ ¬ σ.IsGod true ∧
  (∀ r, InAct false r) ∧ InAct true false ∧
  InPotency true true ∧ ¬ InAct true true ∧
  CausesIn false true esse ∧ Composite true ∧
  ComponentOf true true ∧ PriorSimply false true ∧
  esseOf true ≠ essenceOf true ∧ esseOf false = essenceOf false

def Certificate : Prop := AllPremises ∧ Nonvacuity

def ExactBoundary : Prop := Certificate ↔ TruthCore.Logic.ExcludedMiddle
end TruthCore.Case.Catholicism.ClassicalAttributesJointWitness
