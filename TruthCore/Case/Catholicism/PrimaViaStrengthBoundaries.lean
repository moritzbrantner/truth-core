module

public import TruthCore.Case.Catholicism.StageOne
public import TruthCore.Case.Catholicism.StageOneQuintaVia
public import TruthCore.Greek.Aristotle.Physics.Typed.Motion
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question103.Government
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3Interpretation
public import TruthCore.Logic.ExcludedMiddle

/-!
Typed boundaries for the original independent-potency dictionary. Replacing
an arbitrary relevance predicate by `True` would recover the strong input,
not weaken it. These tests instead leave that predicate independent. They do
not assert anything about every downstream attribute or historical bundle.
-/

@[expose] public section
namespace TruthCore.Case.Catholicism.PrimaViaStrengthBoundaries
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Physics.Typed

/-- The literal being-in-act reduction does not rescue absolute unmovedness
from the weak relevant-respect per-se premise. -/
def WeakBeingInActDoesNotYieldAbsolute : Prop :=
  ¬ ∀ M : MotionModel,
    SomethingIsMovedReading M.MovedIn →
    MovedOnlyAsInPotencyReading M.MovedIn M.InPotency →
    ReducedOnlyByABeingInActReading M.MovedIn M.MovesIn M.InAct →
    NotActAndPotencyInSameRespectReading M.InAct M.InPotency →
    SecondMoversMoveAsMovedInRelevantRespectReading M.MovedIn M.MovesIn M.MovesAsMoved M.RelevantTo →
    NoInfinitePerSeMoverSeriesReading M.MovesAsMoved → AbsoluteConclusion M

/-- The full VII.1 transfer interface fails with only the weak relevant link. -/
def WeakLinkDoesNotYieldLocalRegress : Prop :=
  ¬ ∀ (Being Respect : Type) (IsLocal : Respect → Prop)
    (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (MovesPrimarily MovesAsMoved : Being → Being → Prop)
    (RelevantTo : Being → Being → Respect → Respect → Prop),
    SecondMoversMoveAsMovedInRelevantRespectReading MovedIn MovesIn MovesAsMoved RelevantTo →
    NoInfinitePerSeMoverSeriesReading MovesAsMoved →
    NoInfiniteLocalMovedMoverChainReading IsLocal MovedIn MovesIn MovesPrimarily

/-- III.3 does not supply the missing relevance condition for the VIII.5 transfer. -/
def WeakLinkDoesNotYieldMovedByAnotherRegress : Prop :=
  ¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) (MovesAsMoved : Being → Being → Prop)
    (RelevantTo : Being → Being → Respect → Respect → Prop),
    MovingIsInTheMovedReading MovesIn MovedIn →
    SecondMoversMoveAsMovedInRelevantRespectReading MovedIn MovesIn MovesAsMoved RelevantTo →
    NoInfinitePerSeMoverSeriesReading MovesAsMoved →
    NoInfiniteSeriesOfMoversMovedByAnotherReading MovesIn

/-- A model of the relative conclusion and all the other generic Stage1 inputs
without a God witness. No Fourth-Way or later attribute premises are asserted. -/
def RelativeStageOneCountermodel : Prop :=
  ∃ M : MotionModel, WeakPremises M ∧ RelativeConclusion M ∧
    FirstUnmovedMoverExistsOrNot M.MovedIn M.MovesIn ∧
    AtMostOneFirstUnmovedMover M.MovedIn M.MovesIn ∧
    FirstUnmovedMoverIsPureAct M.MovedIn M.MovesIn (fun _ => False) ∧
    UniquePureActFirstMoverIsGod M.MovedIn M.MovesIn (fun _ => False) (fun _ => False) ∧
    ¬ GodExists (fun _ : M.Being => False)

/-- The director-regress interface with only the relevant-respect link does
not yield an absolutely immobile intelligent director, even retaining its
through-director and unmoved-design bridges. The result assumes EM explicitly. -/
def WeakDirectorLinkDoesNotSuffice : Prop :=
  ¬ ∀ (Being Respect End : Type)
    (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (InPotency InAct : Being → Respect → Prop) (MovesAsMoved : Being → Being → Prop)
    (RelevantTo : Being → Being → Respect → Respect → Prop)
    (NaturalBody HasCognition Intelligent : Being → Prop) (Directs : Being → Being → End → Prop),
    MovedOnlyAsInPotencyReading MovedIn InPotency →
    MovesOnlyAsInActReading MovesIn InAct →
    NotActAndPotencyInSameRespectReading InAct InPotency →
    ReducedOnlyByAMoverReading MovedIn MovesIn →
    SecondMoversMoveAsMovedInRelevantRespectReading MovedIn MovesIn MovesAsMoved RelevantTo →
    NoInfinitePerSeMoverSeriesReading MovesAsMoved → TruthCore.Logic.ExcludedMiddle →
    DirectionPassesToMoversOfDirectors MovesIn Directs →
    UnmovedDirectorKnowsAndUnderstands MovedIn HasCognition Intelligent Directs →
    NaturalDirectionReducedToIntelligentImmobileDirector MovedIn NaturalBody HasCognition Intelligent Directs

/-- Five checked boundaries; each conjunct keeps exactly the scope stated above. -/
def WeakConsumerBoundaries : Prop :=
  WeakBeingInActDoesNotYieldAbsolute ∧ WeakLinkDoesNotYieldLocalRegress ∧
    WeakLinkDoesNotYieldMovedByAnotherRegress ∧ RelativeStageOneCountermodel ∧
    WeakDirectorLinkDoesNotSuffice
end TruthCore.Case.Catholicism.PrimaViaStrengthBoundaries
