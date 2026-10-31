import TruthCore.Causality.RootIntellectWill
import TruthCore.Causality.DirectEsseGenusOmissionControl

/-! Structural omission of ledger L on the unchanged ORIGINAL #681 model.
Only previously unspecified intellect/will predicates are assigned false. All
other fourteen interfaces are checked; in particular q14 is not simply dropped.
Roots are noncomposite but components of the instrument. This is a formal rival,
not metaphysical possibility, full explanation, or an attribution to Aquinas. -/
namespace TruthCore.Causality.RootIntellectWillOmission
open TruthCore.Causality.NecessarySimplePlurality
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.BruteFoundationBoundary (EveryContingentGroundedAt)
open TruthCore.Causality.WholeRosterFoundation (WholeRosterNotTrapped)
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
  (DistinctEsseCauseDichotomyReading EssentialPrinciplesCannotCauseDistinctEsseReading)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)

abbrev model := TruthCore.Causality.DirectEsseGenusOmissionControl.profile
/-- Previously unspecified attribute assignments; no original field changes. -/
def noIntellect : Being → Prop := fun _ => False
def noWill : Being → Prop := fun _ => False

/-- All thirteen nonlogical interfaces other than ledger L. The registered
result additionally retains EM, making all fourteen non-L inputs explicit. -/
def RetainedInputs : Prop :=
  InhabitedConcreteAt model.ontic model.concrete false ∧
  WholeRosterNotTrapped model false ∧ EveryContingentGroundedAt model false ∧
  ExistingInActAt model.ontic esseProfile.InAct esseProfile.esse false ∧
  EsseCauseIsActualConcreteGround model false esseProfile.CausesIn esseProfile.esse ∧
  DistinctEsseCauseDichotomyReading esseProfile ∧
  EssentialPrinciplesCannotCauseDistinctEsseReading esseProfile ∧
  SimplyPriorIsActualConcreteGround model false component ∧
  CompositePosteriorToComponentsReading component component ∧
  CompositeHasComponentOtherThanItselfReading composite component ∧
  MatterFormAndEsseEssenceAreCompositionsReading matterForm composite essence esse ∧
  ImmaterialIsIntellectualReading matterForm noIntellect component ∧
  WillFollowsIntellectReading noIntellect noWill

/-- A SAME selected root is necessary, first, noncomposite and essence/esse
identical, yet enters the instrument's composition. Noncomposition does not
supply remoteness from the composition of others. -/
def RootStructure (n : Being) : Prop :=
  ActualRoot model false n ∧ NecessaryAt model.ontic false n ∧
  IsFirstBeing component n ∧ ¬ composite n ∧ esse n = essence n ∧ component n .instrument

/-- Exact non-L configuration, with both old roots and failure of intellect.
Contingent-ground coverage is vacuous in the old all-present ontology. q14's
antecedent fails for roots because they enter others, and for nonroots because
they are matter-form composites; q19 is vacuous under false intellect. -/
def Control : Prop :=
  JointControl ∧ RetainedInputs ∧ RootStructure .left ∧ RootStructure .right ∧
  Being.left ≠ Being.right ∧ ¬ NoComponentIsFirstBeingReading component component ∧
  ¬ (∃ n, ActualRoot model false n ∧ noIntellect n) ∧
  ¬ TruthCore.Causality.RootIntellectWill.NecessaryRootIntellectWillAt
    model false esseProfile component component composite matterForm noIntellect noWill

end TruthCore.Causality.RootIntellectWillOmission
