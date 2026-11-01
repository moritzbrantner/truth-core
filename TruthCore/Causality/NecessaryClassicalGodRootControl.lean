import TruthCore.Causality.NecessaryClassicalGodRoot
import TruthCore.Causality.RootPositiveIntellectWillControl

/-! Full25 joint compatibility and a necessary non-God effect on the EXACT
old18 concurrent extension. Every NEW signature/potency/infinity/eternity field
is explicit. Empty potency is forced by old all-true act plus exclusivity;
no positive potency, physical/cognitive/moral adequacy or Catholic truth follows. -/
namespace TruthCore.Causality.NecessaryClassicalGodRootControl
open TruthCore.Causality.RootPositiveIntellectWillControl
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Causality.DirectEsseRootPerfectionGoodness
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

/-- All five dictionaries below are NEW assignments, not old role-model facts. -/
def god (x : TransferRole) : Prop := x = .source
def potency (_ : TransferRole) (_ : Bool) : Prop := False
def infinite (x : TransferRole) : Prop := profile.esseOf x = profile.essenceOf x
def eternal (_ : TransferRole) : Prop := True
/-- The primitive field is assigned the EXACT existing nine-predicate package.
This is a fixture assignment, not a definition of the repository signature. -/
def attributes (x : TransferRole) : Prop :=
  NineClassicalAttributes (IsSimple composite) (IsPerfect profile.InAct)
    (IsSupremelyGood profile.InAct transferAct profile.CausesIn profile.esse)
    (IsTheOneGod god) infinite (IsImmutable potency) eternal intellect will x

/-- NEW signature on the same old role carrier. Historical/Creed fields below
are arbitrary unused placeholders, not historical/religious assertions. -/
def signature : Signature where
  Being := TransferRole
  IsGod := god
  HasClassicalAttributes := attributes
  RevealsRecognizably := fun _ => False
  jesus := .recipient
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

/-- Old17 nonlogical interfaces plus the seven new ones. Supplied EM makes the
exact25 route inputs; the old dictionary and model are imported unchanged. -/
def RetainedInputs : Prop :=
  TruthCore.Causality.RootPositiveIntellectWillControl.RetainedInputs ∧
  ActSimplyPriorToPotencyReading profile.InAct potency prior ∧
  NotActAndPotencyInSameRespectReading profile.InAct potency ∧
  SubsistentBeingIsInfiniteReading profile.essenceOf profile.esseOf infinite ∧
  ImmutableIsEternalReading potency eternal ∧
  GodNamesTheFullyDescribedPrinciple profile.InAct (transferMore true) profile.CausesIn
    profile.esse component signature.IsGod ∧
  GodIsMaximalInBeing signature.IsGod profile.InAct (transferMore true) profile.esse ∧
  ClassicalAttributesSuffice signature (IsSimple composite) (IsPerfect profile.InAct)
    (IsSupremelyGood profile.InAct transferAct profile.CausesIn profile.esse)
    (IsTheOneGod signature.IsGod) infinite (IsImmutable potency) eternal intellect will

/-- Exact full25 endpoint BODY at the same old source. -/
def SourceWitness : Prop :=
  PerfectRootAt model false profile.InAct (transferMore true) profile.esse .source ∧
  profile.esseOf .source = profile.essenceOf .source ∧ IsFirstBeing prior .source ∧
  ¬ matterForm .source ∧ RemoteFromAll component .source ∧ signature.IsGod .source ∧
  NineClassicalAttributes (IsSimple composite) (IsPerfect profile.InAct)
    (IsSupremelyGood profile.InAct transferAct profile.CausesIn profile.esse)
    (IsTheOneGod signature.IsGod) infinite (IsImmutable potency) eternal intellect will .source ∧
  signature.HasClassicalAttributes .source

def Control : Prop :=
  TruthCore.Causality.RootPositiveIntellectWillControl.Control ∧ RetainedInputs ∧ SourceWitness ∧
  NecessaryClassicalGodRootAt signature model false profile transferAct potency (transferMore true)
    prior component composite matterForm infinite eternal intellect will ∧
  UniqueClassicalGodExists signature ∧ GodIsOne signature.IsGod ∧
  (∀ x r, ¬ potency x r) ∧ (∀ x, NecessaryAt model.ontic false x) ∧
  (model.concrete .producer ∧ model.ontic.ExistsAt false .producer ∧
    NecessaryAt model.ontic false .producer ∧ ¬ signature.IsGod .producer ∧
    profile.CausesIn .source .producer profile.esse ∧ TransferRole.producer ≠ .source)
end TruthCore.Causality.NecessaryClassicalGodRootControl
