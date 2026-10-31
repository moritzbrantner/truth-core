import TruthCore.Causality.RootPositiveIntellectWill

/-! Positive/discriminating extension of the EXACT #732 concurrent role model.
Only previously unspecified modal/ground, part/priority, represented-map and
cognitive dictionaries are supplied. No old role, act, cause or grade changes.
The component assignment deliberately does NOT impose priority of every part;
its formal satisfaction is not a metaphysical interpretation or adequacy claim. -/
namespace TruthCore.Causality.RootPositiveIntellectWillControl
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.DirectEsseRootPerfectionGoodness
open TruthCore.Causality.RootPositiveIntellectWill
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

def model : Profile Bool TransferRole where
  ontic := { frame := ⟨fun _ _ => True⟩
             ExistsAt := fun _ _ => True
             Causes := fun _ c x => transferCause true c x false }
  concrete := fun _ => True
  grounds := fun _ c x => transferCause true c x false

/-- NEW dictionaries on the old roles, never claimed to be old model fields. -/
def prior (c x : TransferRole) : Prop := transferCause true c x false
def component (c x : TransferRole) : Prop := c = .supporter ∧ x = .producer
def composite (x : TransferRole) : Prop := x = .producer
def matterForm (x : TransferRole) : Prop := x = .producer
def essence (x : TransferRole) : TransferRole := match x with
  | .producer => .source
  | x => x
def esse (x : TransferRole) : TransferRole := x
def intellect (x : TransferRole) : Prop := x = .source ∨ x = .recipient
def will (x : TransferRole) : Prop := intellect x

/-- Profile assembles exact OLD act/cause/esse-respect and explicitly NEW maps.
The unused essential-principles field is false; no q3a4 causal route is assumed. -/
def profile : PrimaPars.Question3.Article4.Profile TransferRole TransferRole Bool where
  InAct := transferAct
  CausesIn := transferCause true
  essenceOf := essence
  esseOf := esse
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := false

/-- Seventeen exact nonlogical inputs of the eighteen-input route. EM remains
an explicit theorem input; no component-priority or distinct-component premise. -/
def RetainedInputs : Prop :=
  InhabitedConcreteAt model.ontic model.concrete false ∧
  WholeRosterNotTrapped model false ∧ EveryContingentGroundedAt model false ∧
  MaximumInBeingCausesAllBeingsReading profile.InAct (transferMore true) profile.CausesIn profile.esse ∧
  ExistingInActAt model.ontic profile.InAct profile.esse false ∧
  EsseCauseIsActualConcreteGround model false profile.CausesIn profile.esse ∧
  GradesToMaximumAtBeing profile.InAct (transferMore true) profile.esse ∧
  ActualityOnlyInsofarAsBeingReading profile.InAct profile.esse ∧
  PerfectionsOfEffectPreexistInCauseReading profile.InAct profile.CausesIn profile.esse ∧
  GoodnessIsActualityReading transferAct profile.InAct ∧
  UniversalCauseTransfersPerfections profile.InAct profile.CausesIn profile.esse ∧
  CompositeHasAUnitingCauseReading composite profile.CausesIn profile.esse ∧
  MatterFormAndEsseEssenceAreCompositionsReading matterForm composite profile.essenceOf profile.esseOf ∧
  SimplyPriorIsActualConcreteGround model false prior ∧
  NoComponentIsFirstBeingReading component prior ∧
  ImmaterialIsIntellectualReading matterForm intellect component ∧
  WillFollowsIntellectReading intellect will

/-- BODY of the exact shared endpoint at the same explicit source. -/
def SourceWitness : Prop :=
  PerfectRootAt model false profile.InAct (transferMore true) profile.esse .source ∧
  IsSupremelyGood profile.InAct transferAct profile.CausesIn profile.esse .source ∧
  profile.esseOf .source = profile.essenceOf .source ∧ IsSimple composite .source ∧
  IsFirstBeing prior .source ∧ ¬ matterForm .source ∧ RemoteFromAll component .source ∧
  intellect .source ∧ will .source

/-- Exact old concurrent certificate plus all18 inputs and their SAME source
endpoint. Positive producer composition/uniter and old secondary activity remain.
The old component-priority principle fails at supporter→producer; no global
weakening, full incomparability, moral/cognitive/physical adequacy is claimed. -/
def Control : Prop :=
  ConcurrentTransferSeparates ∧ RetainedInputs ∧ SourceWitness ∧
  NecessaryPositiveRootIntellectWillAt model false profile transferAct (transferMore true)
    prior component composite matterForm intellect will ∧
  composite .producer ∧ component .supporter .producer ∧
  profile.CausesIn .source .producer profile.esse ∧
  transferCause true .supporter .recipient false ∧ transferCause true .producer .recipient true ∧
  ¬ CompositePosteriorToComponentsReading component prior
end TruthCore.Causality.RootPositiveIntellectWillControl
