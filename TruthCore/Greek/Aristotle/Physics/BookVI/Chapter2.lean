import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter1

namespace TruthCore.Greek.Aristotle.Physics

/-- Every magnitude is divisible into magnitudes in Aristotle, *Physics* VI.2,
232a23-27, because every magnitude is continuous and no continuum is composed of
indivisibles.

Source: Aristotle, *Physics* VI.2, 232a23-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EveryMagnitudeDivisibleIntoMagnitudesReading
    (EveryMagnitudeDivisibleIntoMagnitudes : Prop) : Prop :=
  EveryMagnitudeDivisibleIntoMagnitudes

/-- The faster mover traverses a greater distance in an equal time in Aristotle,
*Physics* VI.2, 232a27-32.

Source: Aristotle, *Physics* VI.2, 232a27-32 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FasterTraversesGreaterDistanceInEqualTimeReading
    (FasterTraversesGreaterDistanceInEqualTime : Prop) : Prop :=
  FasterTraversesGreaterDistanceInEqualTime

/-- The faster mover can traverse a greater distance in less time than the slower
mover in Aristotle, *Physics* VI.2, 232a32-232b5.

Source: Aristotle, *Physics* VI.2, 232a32-232b5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FasterTraversesGreaterDistanceInLessTimeReading
    (FasterTraversesGreaterDistanceInLessTime : Prop) : Prop :=
  FasterTraversesGreaterDistanceInLessTime

/-- The time in which one mover traverses an equal distance relative to another is
either equal, less, or greater in Aristotle's trichotomy argument in *Physics* VI.2,
232b12-20.

Source: Aristotle, *Physics* VI.2, 232b12-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EqualDistanceTimeComparisonTrichotomyReading
    (EqualTime LessTime GreaterTime : Prop) : Prop :=
  EqualTime ∨ LessTime ∨ GreaterTime

/-- For equal distance, the faster mover takes neither equal nor greater time than
the slower mover, since those alternatives would make it equal in speed or slower,
in Aristotle, *Physics* VI.2, 232b12-20.

Source: Aristotle, *Physics* VI.2, 232b12-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FasterExcludesEqualOrGreaterTimeForEqualDistanceReading
    (EqualTime GreaterTime : Prop) : Prop :=
  ¬ EqualTime ∧ ¬ GreaterTime

/-- The faster mover traverses an equal distance in less time than the slower mover
in Aristotle, *Physics* VI.2, 232b5-20.

Source: Aristotle, *Physics* VI.2, 232b5-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FasterTraversesEqualDistanceInLessTimeReading
    (LessTime : Prop) : Prop :=
  LessTime

/-- Every motion occurs in time, movement is possible in any given time, and any
mover can move faster or slower in Aristotle, *Physics* VI.2, 232b20-25.

Source: Aristotle, *Physics* VI.2, 232b20-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionTimeAndVariableSpeedReading
    (EveryMotionOccursInTime MotionPossibleInAnyGivenTime
      EveryMoverCanMoveFasterOrSlower : Prop) : Prop :=
  EveryMotionOccursInTime ∧ MotionPossibleInAnyGivenTime ∧
    EveryMoverCanMoveFasterOrSlower

/-- Aristotle calls continuous what is divisible into things that are themselves
always further divisible in *Physics* VI.2, 232b24-26.

Source: Aristotle, *Physics* VI.2, 232b24-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContinuityAsAlwaysFurtherDivisibleReading
    (Continuous AlwaysFurtherDivisible : Prop) : Prop :=
  Continuous ↔ AlwaysFurtherDivisible

/-- Alternating between the faster and slower mover always produces a further
division of both the traversal time and magnitude in Aristotle, *Physics* VI.2,
232b25-233a9.

Source: Aristotle, *Physics* VI.2, 232b25-233a9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AlternatingSpeedsIndefinitelyDivideTimeMagnitudeReading
    (TimeAlwaysFurtherDivisible MagnitudeAlwaysFurtherDivisible : Prop) : Prop :=
  TimeAlwaysFurtherDivisible ∧ MagnitudeAlwaysFurtherDivisible

/-- Applying Aristotle's definition of continuity to the alternating-speed
construction yields continuity of time and magnitude in *Physics* VI.2,
232b24-233a10.

Source: Aristotle, *Physics* VI.2, 232b24-233a10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AlwaysDivisibleTimeMagnitudeAreContinuousReading
    (TimeAlwaysFurtherDivisible MagnitudeAlwaysFurtherDivisible
      TimeContinuous MagnitudeContinuous : Prop) : Prop :=
  (TimeAlwaysFurtherDivisible ∧ MagnitudeAlwaysFurtherDivisible) →
    (TimeContinuous ∧ MagnitudeContinuous)

/-- Every time and every magnitude are continuous in Aristotle, *Physics* VI.2,
232b24-233a10.

Source: Aristotle, *Physics* VI.2, 232b24-233a10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeAndMagnitudeContinuousReading
    (EveryTimeContinuous EveryMagnitudeContinuous : Prop) : Prop :=
  EveryTimeContinuous ∧ EveryMagnitudeContinuous

/-- Time and magnitude admit the same and equal divisions in Aristotle,
*Physics* VI.2, 233a9-17: half the time corresponds to half the distance, and a
smaller time generally to a smaller distance.

Source: Aristotle, *Physics* VI.2, 233a9-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeMagnitudeHaveSameEqualDivisionsReading
    (TimeMagnitudeHaveSameDivisions TimeMagnitudeHaveEqualDivisions : Prop) : Prop :=
  TimeMagnitudeHaveSameDivisions ∧ TimeMagnitudeHaveEqualDivisions

end TruthCore.Greek.Aristotle.Physics
