import TruthCore.Causality.NecessarySimplePlurality
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article8
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Cause
import TruthCore.Causality.PowerExistenceBoundary
import TruthCore.Causality.NecessarilyUnderived
import TruthCore.Explanation.ExistencePSR
import TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverSimple.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverPureAct.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Solution
import TruthCore.Results.Case.Catholicism.Q11NatureUniqueness.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

/-! A five-being controlled strengthening of the unchanged four-being model.
Efficient cause and priority are strict rank increase; components additionally
have positive rank. This is finite satisfiability of the encoded commitments,
not metaphysical possibility or a complete classical divine model. -/
namespace TruthCore.Causality.PartFreePlurality

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.German.Kant.CosmologicalInference

inductive Being where
  | left | right | constituent | instrument | effect
  deriving DecidableEq

abbrev Respect := TruthCore.Causality.NecessarySimplePlurality.Respect

/-- Explicit recursors keep this finite interpretation zero-axiom: the
equation compiler may use propositional extensionality for overlapping
pattern alternatives in this finite interpretation. -/
def root : Being → Prop :=
  Being.rec (motive := fun _ => Prop) True True False False False

def rank : Being → Nat
  | .left | .right => 0
  | .constituent => 1
  | .instrument => 2
  | .effect => 3

/-- Strict explanatory priority, also selected as efficient cause. This does
not by itself make an efficient cause a part of its effect. -/
def prior (p x : Being) : Prop := rank p < rank x

/-- Proper components are dependent beings; efficient sources need not be parts. -/
def component (p x : Being) : Prop := 0 < rank p ∧ prior p x

def composite (x : Being) : Prop := ∃ p, component p x ∧ p ≠ x
def body (x : Being) : Prop := 0 < rank x
def matterForm (x : Being) : Prop := 1 < rank x

def erase : Being → TruthCore.Causality.NecessarySimplePlurality.Being
  | .left => .left
  | .right => .right
  | .constituent | .instrument => .instrument
  | .effect => .effect

def moved (x : Being) (r : Respect) : Prop :=
  TruthCore.Causality.NecessarySimplePlurality.moved (erase x) r

def moves (y x : Being) (r : Respect) : Prop :=
  TruthCore.Causality.NecessarySimplePlurality.moves (erase y) (erase x) r

def inAct (x : Being) (r : Respect) : Prop :=
  TruthCore.Causality.NecessarySimplePlurality.inAct (erase x) r

def asMoved (y x : Being) : Prop :=
  TruthCore.Causality.NecessarySimplePlurality.asMoved (erase y) (erase x)

def essence : Being → Being
  | .left => .left
  | .right => .right
  | .constituent => .constituent
  | .instrument => .left
  | .effect => .left

def esse : Being → Being := fun x => x
def suppositum : Being → Being := fun x => x

/-- Every candidate is actually present at both universally accessible worlds.
No cause crosses worlds: `prior` is instantiated at each world separately. -/
def ontic : Ontic Bool Being where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := fun _ => prior

def power : TruthCore.Causality.PowerExistenceBoundary.Profile Bool Being where
  ontic := ontic
  transmitsPower := fun _ => prior
  supportsEsse := fun _ => prior
  intrinsicPower := fun _ => root
  properPartOf := component

def explanation : TruthCore.Explanation.ExistencePSR.Model Bool Being where
  ontic := ontic
  explains := fun _ r f => match f with
    | .fact x => r = .intrinsic x

def esseProfile : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile Being Being Respect where
  InAct := inAct
  CausesIn := fun y x _ => prior y x
  essenceOf := essence
  esseOf := esse
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := .esse

/-- Actual causal exercise and composition have positive witnesses; these are
not only universal statements with empty antecedents. -/
def OntologyControl : Prop :=
  (∀ w v, ontic.frame.access w v) ∧
  (∀ w x, ontic.ExistsAt w x) ∧
  NecessaryAt ontic false .left ∧ NecessaryAt ontic false .right ∧
  TruthCore.Causality.PowerExistenceBoundary.Coherent power ∧
  TruthCore.Causality.PowerExistenceBoundary.UnborrowedPowerAt power false .left ∧
  TruthCore.Causality.PowerExistenceBoundary.UnborrowedPowerAt power false .right ∧
  (∀ w, ¬ TruthCore.Causality.PowerExistenceBoundary.ExternallySupportedAt power w .left) ∧
  (∀ w, ¬ TruthCore.Causality.PowerExistenceBoundary.ExternallySupportedAt power w .right) ∧
  (∀ w, ontic.Causes w .left .instrument ∧
    ontic.Causes w .right .instrument ∧ ontic.Causes w .instrument .effect) ∧
  TruthCore.Explanation.ExistencePSR.Sound explanation ∧ TruthCore.Explanation.ExistencePSR.ExistencePSR explanation ∧
  (∀ w x, explanation.explains w (.intrinsic x) (.fact x)) ∧
  TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Coherent esseProfile ∧
  TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.DistinctEsseAt esseProfile .instrument ∧
  TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.DistinctEsseAt esseProfile .effect ∧
  TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.DistinctEsseCauseDichotomyReading esseProfile ∧
  TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.EssentialPrinciplesCannotCauseDistinctEsseReading esseProfile

/-- The actual first-way and simplicity inputs are exposed so the scope of
this joint interpretation is checkable. Pure act and simplicity are conclusions
of imported theorems, not definitions of `root`. -/
def SimplicityControl : Prop :=
  SomethingIsMovedReading moved ∧
  MovedOnlyAsInPotencyReading moved moved ∧
  MovesOnlyAsInActReading moves inAct ∧
  ReducedOnlyByAMoverReading moved moves ∧
  NotActAndPotencyInSameRespectReading inAct moved ∧
  SecondMoversMoveOnlyAsMovedReading moved moves asMoved ∧
  NoInfinitePerSeMoverSeriesReading asMoved ∧
  ActSimplyPriorToPotencyReading inAct moved prior ∧
  FirstUnmovedMoverIsFirstBeing moved moves prior ∧
  NoBodyMovesUnlessMovedReading moved moves body ∧
  CompositePosteriorToComponentsReading component prior ∧
  CompositeHasComponentOtherThanItselfReading composite component ∧
  MatterFormAndEsseEssenceAreCompositionsReading matterForm composite essence esse ∧
  FirstUnmovedMoverIsSimpleReading moved moves body matterForm composite essence esse ∧
  FirstUnmovedMoverIsPureAct moved moves (PureAct moved) ∧
  FirstUnmovedMoverHasEveryPerfection moved moves inAct ∧
  IsFirstUnmovedMover moved moves .left ∧
  IsFirstUnmovedMover moved moves .right ∧
  asMoved .instrument .effect ∧ composite .instrument ∧ composite .effect

/-- `root` instantiates the Q11 theorem's predicate parameter, not the Catholic
identification `IsGod`. The common-nature and differentiation premises fail in
this very same interpretation. Adding either, with its other existing inputs,
would exclude it. No independent defense of those premises is asserted. -/
def UniquenessControl : Prop :=
  Being.left ≠ Being.right ∧
  ¬ AtMostOneFirstUnmovedMover moved moves ∧
  IndividuatingBasisIsIncommunicableReading suppositum ∧
  GodSuppositumIsNatureReading root suppositum essence ∧
  (∀ deity, ¬ ProperGodInstancesHaveCommonNatureReading root essence deity) ∧
  ¬ PluralFirstMoversWouldDifferInActReading moved moves inAct

def JointControl : Prop := OntologyControl ∧ SimplicityControl ∧ UniquenessControl ∧
  NoComponentIsFirstBeingReading component prior ∧
  (∀ x, ¬ component .left x ∧ ¬ component .right x) ∧
  CompositeHasAUnitingCauseReading composite esseProfile.CausesIn TruthCore.Causality.NecessarySimplePlurality.Respect.esse

end TruthCore.Causality.PartFreePlurality
