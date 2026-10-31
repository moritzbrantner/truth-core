import TruthCore.Causality.RootIntellectWillPureAct
import TruthCore.Causality.StrictPriorityPureAct
import TruthCore.Causality.PartFreePlurality

/-! Positive joint configuration on the UNCHANGED five-being part-free
strengthening (#684), not the original four-being #681 interpretation.
No metaphysical possibility or explanatory/cognitive adequacy is asserted. -/
namespace TruthCore.Causality.RootIntellectWillPureActPlurality
open TruthCore.Causality.PartFreePlurality
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.StrictPriorityPureAct (StrictSimplePriority)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (IsSimple RemoteFromAll)

/-- View of old fields only; all old candidates are stipulated concrete.
No new causal relation or identification beyond this fixture is asserted. -/
def model : Profile Bool Being where
  ontic := ontic
  concrete := fun _ => True
  grounds := power.supportsEsse
/-- Newly specified positive attributes, with all old fields unchanged.
These predicates do not encode cognition, appetite or their adequacy. -/
def hasIntellect : Being → Prop := root
def hasWill : Being → Prop := root

/-- Exact ten nonlogical inputs of RootIntellectWillReduced, plus act-priority
and BOTH replacement conditions. With supplied EM these jointly realize both
thirteen-input routes; their combined fourteen-input union is not miscounted. -/
def RetainedInputs : Prop :=
  InhabitedConcreteAt model.ontic model.concrete false ∧
  WholeRosterNotTrapped model false ∧ EveryContingentGroundedAt model false ∧
  SimplyPriorIsActualConcreteGround model false prior ∧
  CompositePosteriorToComponentsReading component prior ∧
  CompositeHasComponentOtherThanItselfReading composite component ∧
  MatterFormAndEsseEssenceAreCompositionsReading matterForm composite essence esse ∧
  NoComponentIsFirstBeingReading component prior ∧
  ImmaterialIsIntellectualReading matterForm hasIntellect component ∧
  WillFollowsIntellectReading hasIntellect hasWill ∧
  ActSimplyPriorToPotencyReading inAct moved prior ∧
  StrictSimplePriority prior ∧ NotActAndPotencyInSameRespectReading inAct moved

/-- The BODY of the shared existential joint endpoint, instantiated at an
explicit individual so that TWO witnesses cannot collapse into two unrelated
existential claims. No independent notion of qualified divinity is introduced. -/
def Witness (n : Being) : Prop :=
  ActualRoot model false n ∧ NecessaryAt model.ontic false n ∧
  esse n = essence n ∧ IsSimple composite n ∧ IsFirstBeing prior n ∧
  ¬ matterForm n ∧ RemoteFromAll component n ∧ hasIntellect n ∧ hasWill n ∧ PureAct moved n

/-- All old commitments survive, both exact route bundles hold, and TWO distinct
actual necessary roots each realize the whole joint attribute tuple. Nonroot
potency, actual causal exercise and composition have explicit positive witnesses.
Contingent grounding is vacuous in the old all-present ontology. -/
def Control : Prop :=
  JointControl ∧ RetainedInputs ∧ Witness .left ∧ Witness .right ∧
  Being.left ≠ Being.right ∧
  TruthCore.Causality.RootIntellectWillPureAct.NecessaryRootIntellectWillPureActAt
    model false esseProfile prior component composite matterForm hasIntellect hasWill moved ∧
  moved .constituent .drive ∧ moved .instrument .drive ∧
  ontic.Causes false .left .instrument ∧ moves .left .instrument .drive ∧
  component .constituent .instrument
end TruthCore.Causality.RootIntellectWillPureActPlurality
