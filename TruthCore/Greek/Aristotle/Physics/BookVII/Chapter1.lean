import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter10

namespace TruthCore.Greek.Aristotle.Physics

/-- If a moving thing does not have the source of its motion in itself, it is
plainly moved by something else, in Aristotle, *Physics* VII.1, 241b24-27.

Source: Aristotle, *Physics* VII.1, 241b24-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoInternalMotionPrincipleRequiresOtherMoverReading
    (LacksInternalMotionPrinciple MovedBySomethingElse : Prop) : Prop :=
  LacksInternalMotionPrinciple → MovedBySomethingElse

/-- For the internal-principle case, Aristotle selects a whole moving in its own
right rather than merely because something belonging to it moves, in *Physics*
VII.1, 241b27-33.

Source: Aristotle, *Physics* VII.1, 241b27-33 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PrimaryPerSeMotionNotMerelyPartMotionReading
    (MovesPerSeAndPrimarily MovesMerelyThroughPart : Prop) : Prop :=
  MovesPerSeAndPrimarily → ¬ MovesMerelyThroughPart

/-- The absence of an external mover does not by itself settle which internal
part is mover and which is moved, so it does not establish undifferentiated
self-motion of the whole, in Aristotle, *Physics* VII.1, 241b33-35.

Source: Aristotle, *Physics* VII.1, 241b33-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoExternalMoverDoesNotSettleInternalMoverMovedReading
    (InferenceToUndifferentiatedSelfMotionInvalid : Prop) : Prop :=
  InferenceToUndifferentiatedSelfMotionInvalid

/-- If a thing comes to rest because something else has ceased moving, that
dependence shows that the thing is moved by something, in Aristotle,
*Physics* VII.1, 242a1-4.

Source: Aristotle, *Physics* VII.1, 242a1-4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RestDependenceEntailsMovedBySomethingReading
    (PartRestDeterminesWholeRest WholeMovedBySomething : Prop) : Prop :=
  PartRestDeterminesWholeRest → WholeMovedBySomething

/-- Dividing a primary per-se moving whole shows that if the selected part does
not move, the whole does not move; otherwise only the other part would be moving
and the whole would not be moving primarily in its own right, in Aristotle,
*Physics* VII.1, 242a4-13.

Source: Aristotle, *Physics* VII.1, 242a4-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DivisiblePrimaryMoverHasRestDeterminingPartReading
    (MovingSubjectDivisible PartRestDeterminesWholeRest : Prop) : Prop :=
  MovingSubjectDivisible → PartRestDeterminesWholeRest

/-- Every moving thing is moved by something, in Aristotle, *Physics* VII.1,
241b24-242a15. “Something” does not yet identify the first mover reached by the
chapter's following regress argument.

Typed sibling reading over the act/potency vocabulary:
`TruthCore.Greek.Aristotle.Physics.Typed.EveryMovedThingHasSomeMoverReading` (docs/typed-physics.md).

Source: Aristotle, *Physics* VII.1, 241b24-242a15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EveryMovingThingMovedBySomethingReading
    (EveryMovingThingMovedBySomething : Prop) : Prop :=
  EveryMovingThingMovedBySomething

/-- Denying a first mover turns the moved-mover series into an infinite chain in
which A is moved by B, B by C, and so on, in Aristotle, *Physics* VII.1,
242a16-24.

Source: Aristotle, *Physics* VII.1, 242a16-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoFirstMoverHypothesisProducesInfiniteChainReading
    (NoFirstMover InfiniteMovedMoverChain : Prop) : Prop :=
  NoFirstMover → InfiniteMovedMoverChain

/-- Because each moved mover moves and is moved simultaneously, all the motions in
the hypothesized chain are simultaneous, in Aristotle, *Physics* VII.1,
242a20-30.

Source: Aristotle, *Physics* VII.1, 242a20-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MovedMoverChainMotionsAreSimultaneousReading
    (InfiniteMovedMoverChain AllChainMotionsSimultaneous : Prop) : Prop :=
  InfiniteMovedMoverChain → AllChainMotionsSimultaneous

/-- Each mover's motion can be taken as numerically one because it is from one
numerical source to one numerical terminus in one numerical time and is not
infinite in its termini, in Aristotle, *Physics* VII.1, 242a30-242b7.

Source: Aristotle, *Physics* VII.1, 242a30-242b7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EachChainMotionNumericallyOneWithFiniteTerminiReading
    (OneNumericalSource OneNumericalTerminus OneNumericalTime
      MotionNotInfiniteInTermini MotionNumericallyOne : Prop) : Prop :=
  OneNumericalSource ∧ OneNumericalTerminus ∧ OneNumericalTime ∧
    MotionNotInfiniteInTermini ∧ MotionNumericallyOne

/-- Motions may be the same generically by category, specifically by specifically
identical termini, or numerically by numerically identical termini and time, in
Aristotle, *Physics* VII.1, 242a30-242b7.

Source: Aristotle, *Physics* VII.1, 242a30-242b7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionUnityGenericSpecificNumericalReading
    (GenericUnityByCategory SpecificUnityByTerminusSpecies
      NumericalUnityByTerminiAndTime : Prop) : Prop :=
  GenericUnityByCategory ∧ SpecificUnityByTerminusSpecies ∧
    NumericalUnityByTerminiAndTime

/-- The finite motion selected for A occupies a finite time, in Aristotle,
*Physics* VII.1, 242b7-11.

Source: Aristotle, *Physics* VII.1, 242b7-11 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FiniteSelectedMotionHasFiniteTimeReading
    (SelectedMotionFinite SelectedMotionTimeFinite : Prop) : Prop :=
  SelectedMotionFinite → SelectedMotionTimeFinite

/-- On the hypothesized infinite chain, the aggregate of the individual motions
would be infinite if the motions are equal or later motions are greater, in
Aristotle, *Physics* VII.1, 242b11-16.

Source: Aristotle, *Physics* VII.1, 242b11-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteChainYieldsInfiniteAggregateMotionReading
    (InfiniteMovedMoverChain EqualOrGreaterMotions
      AggregateMotionInfinite : Prop) : Prop :=
  InfiniteMovedMoverChain ∧ EqualOrGreaterMotions → AggregateMotionInfinite

/-- Since all the individual motions are simultaneous, the apparent reductio puts
their infinite aggregate into the finite time of A's motion, in Aristotle,
*Physics* VII.1, 242b16-18.

Source: Aristotle, *Physics* VII.1, 242b16-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ApparentReductioPutsInfiniteAggregateInFiniteTimeReading
    (AllChainMotionsSimultaneous AggregateMotionInfinite
      SelectedMotionTimeFinite InfiniteAggregateInFiniteTime : Prop) : Prop :=
  AllChainMotionsSimultaneous ∧ AggregateMotionInfinite ∧
    SelectedMotionTimeFinite → InfiniteAggregateInFiniteTime

/-- The initial simultaneous-motion reductio succeeds only if an infinite aggregate
of many subjects' motions in one finite time is impossible, in Aristotle's
diagnosis in *Physics* VII.1, 242b19-23.

Source: Aristotle, *Physics* VII.1, 242b19-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InitialReductioRequiresAggregateImpossibilityReading
    (InitialReductioSucceeds InfiniteAggregateManySubjectsInFiniteTimeImpossible
      : Prop) : Prop :=
  InitialReductioSucceeds → InfiniteAggregateManySubjectsInFiniteTimeImpossible

/-- Infinitely many motions of different subjects may occur in a finite time, since
each subject undergoes its own motion and many things may move simultaneously, in
Aristotle, *Physics* VII.1, 242b19-23.

Source: Aristotle, *Physics* VII.1, 242b19-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteAggregateManySubjectsInFiniteTimePossibleReading
    (InfiniteAggregateManySubjectsInFiniteTimeImpossible : Prop) : Prop :=
  ¬ InfiniteAggregateManySubjectsInFiniteTimeImpossible

/-- The initial simultaneous-motion reductio does not prove that the moved-mover
series has a first member, in Aristotle, *Physics* VII.1, 242b19-23. Aristotle
immediately repairs the proof by adding contact or continuity.

Source: Aristotle, *Physics* VII.1, 242b19-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InitialSimultaneousMotionReductioFailsReading
    (InitialReductioSucceeds : Prop) : Prop :=
  ¬ InitialReductioSucceeds

/-- A primary bodily mover in locomotion must touch or be continuous with what it
moves, in Aristotle, *Physics* VII.1, 242b23-27.

Typed sibling reading over the act/potency vocabulary:
`TruthCore.Greek.Aristotle.Physics.Typed.PrimaryLocalMoverTouchesReading` (docs/typed-physics.md).

Source: Aristotle, *Physics* VII.1, 242b23-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PrimaryBodilyMoverTouchesOrIsContinuousReading
    (TouchesMovedBody ContinuousWithMovedBody : Prop) : Prop :=
  TouchesMovedBody ∨ ContinuousWithMovedBody

/-- Applying contact or continuity throughout the hypothesized moved-mover chain
makes all its members one bodily unity, in Aristotle, *Physics* VII.1,
242b23-27.

Typed sibling reading over the act/potency vocabulary:
`TruthCore.Greek.Aristotle.Physics.Typed.TouchingChainFormsOneReading` (docs/typed-physics.md).

Source: Aristotle, *Physics* VII.1, 242b23-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteMovedMoverChainFormsOneUnityReading
    (InfiniteMovedMoverChain ChainFormsOneBodilyUnity : Prop) : Prop :=
  InfiniteMovedMoverChain → ChainFormsOneBodilyUnity

/-- Whether the bodily unity formed by the chain is finite or infinite makes no
difference to the corrected reductio, in Aristotle, *Physics* VII.1,
242b27-29.

Source: Aristotle, *Physics* VII.1, 242b27-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChainUnityFiniteOrInfiniteSameForReductioReading
    (FiniteUnityCaseCovered InfiniteUnityCaseCovered : Prop) : Prop :=
  FiniteUnityCaseCovered ∧ InfiniteUnityCaseCovered

/-- If the infinite moved-mover chain forms one bodily unity, that single unity
would undergo the chain's infinite motion in the finite time K, in Aristotle,
*Physics* VII.1, 242b27-243a1.

Typed sibling reading over the act/potency vocabulary:
`TruthCore.Greek.Aristotle.Physics.Typed.OneOfInfiniteLocalChainTraversesInfiniteReading` (docs/typed-physics.md).

Source: Aristotle, *Physics* VII.1, 242b27-243a1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChainUnityWouldTraverseInfiniteMotionInFiniteTimeReading
    (InfiniteMovedMoverChain ChainFormsOneBodilyUnity
      OneUnityTraversesInfiniteMotionInFiniteTime : Prop) : Prop :=
  InfiniteMovedMoverChain ∧ ChainFormsOneBodilyUnity →
    OneUnityTraversesInfiniteMotionInFiniteTime

/-- A theoretically possible hypothesis must not produce an impossible result, so
it is enough that the corrected reductio selects one possible equal-or-greater
motion configuration, in Aristotle, *Physics* VII.1, 242b27-243a2.

Source: Aristotle, *Physics* VII.1, 242b27-243a2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PossibleHypothesisMustNotYieldImpossibleReading
    (HypothesisPossible HypothesisYieldsImpossible : Prop) : Prop :=
  HypothesisPossible → ¬ HypothesisYieldsImpossible

/-- The moved-mover series cannot lack a first mover and a first moved subject, in
Aristotle, *Physics* VII.1, 242b23-243a2. This does not yet identify the first
mover as unmoved or give it a theological description.

Typed sibling reading over the act/potency vocabulary:
`TruthCore.Greek.Aristotle.Physics.Typed.NoInfiniteLocalMovedMoverChainReading` (docs/typed-physics.md).

Source: Aristotle, *Physics* VII.1, 242b23-243a2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MovedMoverSeriesCannotLackFirstReading
    (NoFirstMoverOrMoved : Prop) : Prop :=
  ¬ NoFirstMoverOrMoved

end TruthCore.Greek.Aristotle.Physics
