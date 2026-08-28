import TruthCore.Greek.Aristotle.Physics.BookV.Chapter6

namespace TruthCore.Greek.Aristotle.Physics

/-- Aristotle distinguishes continuous, touching, and successive items in *Physics*
VI.1, 231a21-24: continuous things have one common extremity, touching things have
their extremities together, and successive things have nothing homogeneous between.

Source: Aristotle, *Physics* VI.1, 231a21-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContinuousTouchingSuccessiveDistinctionReading
    (ContinuousHaveOneExtremity TouchingHaveExtremitiesTogether
      SuccessiveHaveNothingHomogeneousBetween : Prop) : Prop :=
  ContinuousHaveOneExtremity ∧ TouchingHaveExtremitiesTogether ∧
    SuccessiveHaveNothingHomogeneousBetween

/-- Aristotle's compositional premise in *Physics* VI.1, 231a24-231b6: if a
continuum were composed of indivisibles, those indivisibles would have to form the
continuum through continuity or contact.

Source: Aristotle, *Physics* VI.1, 231a24-231b6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContinuumFromIndivisiblesRequiresContinuityOrContactReading
    (ContinuumComposedOfIndivisibles
      IndivisiblesComposeContinuumThroughContinuityOrContact : Prop) : Prop :=
  ContinuumComposedOfIndivisibles →
    IndivisiblesComposeContinuumThroughContinuityOrContact

/-- Indivisibles cannot compose a continuum through continuity or contact in
Aristotle, *Physics* VI.1, 231a24-231b6. Indivisibles have no distinct extremities,
and whole-to-whole contact does not yield a continuum with distinct parts.

Source: Aristotle, *Physics* VI.1, 231a24-231b6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IndivisiblesCannotComposeContinuumByContinuityOrContactReading
    (IndivisiblesComposeContinuumThroughContinuityOrContact : Prop) : Prop :=
  ¬ IndivisiblesComposeContinuumThroughContinuityOrContact

/-- No continuum is composed of indivisibles in Aristotle, *Physics* VI.1,
231a24-231b6; in particular, a line is not composed of points.

Source: Aristotle, *Physics* VI.1, 231a24-231b6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContinuumNotComposedOfIndivisiblesReading
    (ContinuumComposedOfIndivisibles : Prop) : Prop :=
  ¬ ContinuumComposedOfIndivisibles

/-- A point is not successive to a point, nor a now to a now, in Aristotle,
*Physics* VI.1, 231b6-12, because a line always lies between points and time between
nows; points and nows therefore cannot compose length or time by succession.

Source: Aristotle, *Physics* VI.1, 231b6-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PointAndNowNotSuccessiveReading
    (PointSuccessiveToPoint NowSuccessiveToNow : Prop) : Prop :=
  ¬ PointSuccessiveToPoint ∧ ¬ NowSuccessiveToNow

/-- Every continuum is divisible into things that are themselves always further
divisible, not into indivisibles, in Aristotle, *Physics* VI.1, 231b12-18.

Source: Aristotle, *Physics* VI.1, 231b12-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EveryContinuumDivisibleIntoAlwaysDivisiblesReading
    (EveryContinuumDivisibleIntoAlwaysDivisibles : Prop) : Prop :=
  EveryContinuumDivisibleIntoAlwaysDivisibles

/-- Magnitude, motion, and time stand or fall together with respect to composition
from, and division into, indivisibles in Aristotle, *Physics* VI.1, 231b18-20.

Source: Aristotle, *Physics* VI.1, 231b18-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MagnitudeMotionTimeIndivisibilityInterdependenceReading
    (MagnitudeComposedOfIndivisibles MotionComposedOfIndivisibles
      TimeComposedOfIndivisibles : Prop) : Prop :=
  (MagnitudeComposedOfIndivisibles ↔ MotionComposedOfIndivisibles) ∧
    (MotionComposedOfIndivisibles ↔ TimeComposedOfIndivisibles)

/-- If a magnitude is composed of indivisible parts, the motion over it has
corresponding equal indivisible motion-parts in Aristotle, *Physics* VI.1,
231b20-28.

Source: Aristotle, *Physics* VI.1, 231b20-28 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionPartsCorrespondToMagnitudePartsReading
    (MagnitudeComposedOfIndivisibleParts
      MotionComposedOfCorrespondingIndivisibleParts : Prop) : Prop :=
  MagnitudeComposedOfIndivisibleParts →
    MotionComposedOfCorrespondingIndivisibleParts

/-- While traversing a route, a thing cannot at once be traversing it and already
have traversed the very route it is then traversing in Aristotle, *Physics* VI.1,
231b28-232a5.

Source: Aristotle, *Physics* VI.1, 231b28-232a5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TraversalNotSimultaneouslyUnderwayAndCompleteReading
    (TraversalUnderway TraversalAlreadyComplete : Prop) : Prop :=
  TraversalUnderway → ¬ TraversalAlreadyComplete

/-- On the hypothesis of an indivisible segment, traversal of it would be complete
without ever being underway over that segment in Aristotle, *Physics* VI.1,
232a1-10; something would have walked a distance without walking it.

Source: Aristotle, *Physics* VI.1, 232a1-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IndivisibleTraversalCompletedWithoutTraversingReading
    (IndivisibleSegmentTraversalComplete
      IndivisibleSegmentTraversalEverUnderway : Prop) : Prop :=
  IndivisibleSegmentTraversalComplete ∧
    ¬ IndivisibleSegmentTraversalEverUnderway

/-- If every indivisible segment is crossed without motion being underway on it,
the mover rests at every segment while moving over the whole and so continuously
rests while moving in Aristotle, *Physics* VI.1, 232a10-14.

Source: Aristotle, *Physics* VI.1, 232a10-14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IndivisibleSegmentsCauseRestWhileMovingReading
    (RestsAtEveryIndivisibleSegment MovesOverWhole
      ContinuouslyRestsWhileMoving : Prop) : Prop :=
  (RestsAtEveryIndivisibleSegment ∧ MovesOverWhole) →
    ContinuouslyRestsWhileMoving

/-- Aristotle's dilemma in *Physics* VI.1, 232a14-16: if the proposed indivisible
parts are motions, motion may be present while the subject rests; if they are not
motions, motion is not composed of motions.

Source: Aristotle, *Physics* VI.1, 232a14-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IndivisibleMotionPartsDilemmaReading
    (IndivisiblePartsAreMotions RestPossibleWhileMotionPresent
      MotionNotComposedOfMotions : Prop) : Prop :=
  (IndivisiblePartsAreMotions → RestPossibleWhileMotionPresent) ∧
    (¬ IndivisiblePartsAreMotions → MotionNotComposedOfMotions)

/-- Indivisible length and motion would require indivisible time composed of
indivisible nows in Aristotle, *Physics* VI.1, 232a16-18.

Source: Aristotle, *Physics* VI.1, 232a16-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IndivisibleLengthMotionRequireIndivisibleTimeReading
    (LengthAndMotionComposedOfIndivisibles TimeComposedOfIndivisibleNows : Prop) : Prop :=
  LengthAndMotionComposedOfIndivisibles → TimeComposedOfIndivisibleNows

/-- Dividing the time in which an equal-speed mover traverses a supposedly
indivisible segment divides the corresponding traversal, contradicting its
indivisibility, in Aristotle, *Physics* VI.1, 232a18-22.

Source: Aristotle, *Physics* VI.1, 232a18-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DivisibleTimeDividesMotionOverSegmentReading
    (TraversalTimeDivisible MotionOverSegmentDivisible : Prop) : Prop :=
  TraversalTimeDivisible → MotionOverSegmentDivisible

/-- Magnitude, motion, and time are not composed of indivisibles in Aristotle,
*Physics* VI.1, 231b18-232a22.

Source: Aristotle, *Physics* VI.1, 231b18-232a22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MagnitudeMotionTimeNotComposedOfIndivisiblesReading
    (MagnitudeComposedOfIndivisibles MotionComposedOfIndivisibles
      TimeComposedOfIndivisibles : Prop) : Prop :=
  ¬ MagnitudeComposedOfIndivisibles ∧ ¬ MotionComposedOfIndivisibles ∧
    ¬ TimeComposedOfIndivisibles

end TruthCore.Greek.Aristotle.Physics
