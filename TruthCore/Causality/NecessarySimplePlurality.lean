import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Cause
import TruthCore.Causality.PowerExistenceBoundary
import TruthCore.Causality.NecessarilyUnderived
import TruthCore.Explanation.ExistencePSR
import TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverSimple.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverPureAct.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Solution
import TruthCore.Results.Case.Catholicism.Q11NatureUniqueness.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

/-!
A joint finite interpretation for #320, using existing interfaces rather than
an opaque `Simple` or `God` flag. Two rigid roots have a common instrument and
effect. Component priority derives the existing first-mover simplicity reading;
the act/potency premises derive the existing pure-act reading. Neither inference
provides common nature or differentiation in act.

This is not a metaphysical possibility proof. `Respect` contains exactly the
three represented respects. The primitive matter/form predicate is constrained
by the existing inclusion principle, not a complete theory of hylomorphism.
Genus/difference, subject/accident and adequacy of intrinsic explanation are not
encoded. In particular the PSR tokens below are only sound candidate assignments.
The source readings reused here remain open; no new historical claim is made.
-/
namespace TruthCore.Causality.NecessarySimplePlurality

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.German.Kant.CosmologicalInference

inductive Being where
  | left | right | instrument | effect
  deriving DecidableEq

inductive Respect where
  | esse | drive | heat
  deriving DecidableEq

/-- Explicit recursors keep this finite interpretation zero-axiom: the
equation compiler may use propositional extensionality for overlapping
pattern alternatives in this finite interpretation. -/
def root : Being → Prop :=
  Being.rec (motive := fun _ => Prop) True True False False

def rank : Being → Nat
  | .left | .right => 0
  | .instrument => 1
  | .effect => 2

/-- Strict component priority: both independent roots are components of the
instrument and effect, and the instrument is a component of the effect. -/
def component (p x : Being) : Prop := rank p < rank x

def composite (x : Being) : Prop := ∃ p, component p x ∧ p ≠ x
def body (x : Being) : Prop := 0 < rank x
def matterForm (x : Being) : Prop := 0 < rank x

def moved : Being → Respect → Prop :=
  Being.rec (motive := fun _ => Respect → Prop)
    (fun _ => False) (fun _ => False)
    (Respect.rec (motive := fun _ => Prop) False True False)
    (Respect.rec (motive := fun _ => Prop) False False True)

def moves : Being → Being → Respect → Prop :=
  let toInstrument := Being.rec (motive := fun _ => Respect → Prop)
    (fun _ => False) (fun _ => False)
    (Respect.rec (motive := fun _ => Prop) False True False) (fun _ => False)
  let toEffect := Being.rec (motive := fun _ => Respect → Prop)
    (fun _ => False) (fun _ => False) (fun _ => False)
    (Respect.rec (motive := fun _ => Prop) False False True)
  Being.rec (motive := fun _ => Being → Respect → Prop)
    toInstrument toInstrument toEffect (fun _ _ => False)

def inAct : Being → Respect → Prop :=
  Being.rec (motive := fun _ => Respect → Prop)
    (fun _ => True) (fun _ => True)
    (Respect.rec (motive := fun _ => Prop) True False True)
    (Respect.rec (motive := fun _ => Prop) True False False)

def asMoved : Being → Being → Prop :=
  Being.rec (motive := fun _ => Being → Prop)
    (fun _ => False) (fun _ => False)
    (Being.rec (motive := fun _ => Prop) False False False True) (fun _ => False)

def essence : Being → Being
  | .left => .left
  | .right => .right
  | .instrument => .left
  | .effect => .left

def esse : Being → Being := fun x => x
def suppositum : Being → Being := fun x => x

/-- Every candidate is actually present at both universally accessible worlds.
No cause crosses worlds: `component` is instantiated at each world separately. -/
def ontic : Ontic Bool Being where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := fun _ => component

def power : TruthCore.Causality.PowerExistenceBoundary.Profile Bool Being where
  ontic := ontic
  transmitsPower := fun _ => component
  supportsEsse := fun _ => component
  intrinsicPower := fun _ => root
  properPartOf := component

def explanation : TruthCore.Explanation.ExistencePSR.Model Bool Being where
  ontic := ontic
  explains := fun _ r f => match f with
    | .fact x => r = .intrinsic x

def esseProfile : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile Being Being Respect where
  InAct := inAct
  CausesIn := fun y x _ => component y x
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
  ActSimplyPriorToPotencyReading inAct moved component ∧
  FirstUnmovedMoverIsFirstBeing moved moves component ∧
  NoBodyMovesUnlessMovedReading moved moves body ∧
  CompositePosteriorToComponentsReading component component ∧
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

def JointControl : Prop := OntologyControl ∧ SimplicityControl ∧ UniquenessControl

end TruthCore.Causality.NecessarySimplePlurality
