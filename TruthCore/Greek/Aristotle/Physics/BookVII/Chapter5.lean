import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter4

namespace TruthCore.Greek.Aristotle.Physics

/-- A mover always moves something, does so in time, and moves it through some
distance; while it is moving, some distance has been traversed in some time, in
Aristotle, *Physics* VII.5, 249b27-30.

Source: Aristotle, *Physics* VII.5, 249b27-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MoverMotionHasSubjectTimeDistanceReading
    (MoverActsOnSomething MotionOccursInTime MotionTraversesSomeDistance
      ActiveMovingHasCompletedSomeMotion : Prop) : Prop :=
  MoverActsOnSomething ∧ MotionOccursInTime ∧
    MotionTraversesSomeDistance ∧ ActiveMovingHasCompletedSomeMotion

/-- If a force moves a load through a distance in a time, the same force moves
half the load through twice the distance in the same time, in Aristotle,
*Physics* VII.5, 249b30-250a3.

This records Aristotle's stated proportional rule in its own setup; the
threshold qualifications later in the chapter are not erased.

Source: Aristotle, *Physics* VII.5, 249b30-250a3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SameForceHalfLoadDoubleDistanceSameTimeReading
    (BaselineForceLoadDistanceTime
      SameForceHalfLoadDoubleDistanceSameTime : Prop) : Prop :=
  BaselineForceLoadDistanceTime →
    SameForceHalfLoadDoubleDistanceSameTime

/-- If a force moves a load through a distance in a time, the same force moves
half the load through that distance in half the time, in Aristotle, *Physics*
VII.5, 249b30-250a3.

Source: Aristotle, *Physics* VII.5, 249b30-250a3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SameForceHalfLoadSameDistanceHalfTimeReading
    (BaselineForceLoadDistanceTime
      SameForceHalfLoadSameDistanceHalfTime : Prop) : Prop :=
  BaselineForceLoadDistanceTime →
    SameForceHalfLoadSameDistanceHalfTime

/-- Halving both force and load preserves their force-to-load ratio, in
Aristotle's proportional setup in *Physics* VII.5, 250a3-8.

Source: Aristotle, *Physics* VII.5, 250a3-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def HalfForceHalfLoadPreserveForceLoadRatioReading
    (HalfForceAndHalfLoad ForceLoadRatioPreserved : Prop) : Prop :=
  HalfForceAndHalfLoad → ForceLoadRatioPreserved

/-- Within Aristotle's proportional setup, preserving the force-to-load ratio
preserves the traversed distance and elapsed time, in *Physics* VII.5,
250a3-8.

Source: Aristotle, *Physics* VII.5, 250a3-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PreservedForceLoadRatioEntailsSameDistanceTimeReading
    (ForceLoadRatioPreserved SameDistanceAndTime : Prop) : Prop :=
  ForceLoadRatioPreserved → SameDistanceAndTime

/-- Halving both force and load therefore preserves the distance traversed in
the same time, within Aristotle's proportional setup in *Physics* VII.5,
250a3-8.

Source: Aristotle, *Physics* VII.5, 250a3-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def HalfForceHalfLoadSameMotionReading
    (HalfForceAndHalfLoad SameDistanceAndTime : Prop) : Prop :=
  HalfForceAndHalfLoad → SameDistanceAndTime

end TruthCore.Greek.Aristotle.Physics
