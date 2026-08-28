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

/-- Time and magnitude are infinite together and in the same respect in Aristotle,
*Physics* VI.2, 233a17-21: by their extremities, by division, or in both ways.

Source: Aristotle, *Physics* VI.2, 233a17-21 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeMagnitudeInfinityMatchesBySenseReading
    (TimeInfiniteByExtent MagnitudeInfiniteByExtent TimeInfiniteByDivision
      MagnitudeInfiniteByDivision : Prop) : Prop :=
  (TimeInfiniteByExtent ↔ MagnitudeInfiniteByExtent) ∧
    (TimeInfiniteByDivision ↔ MagnitudeInfiniteByDivision)

/-- Magnitude, time, and every continuum may be called infinite either by division
or by their extremities in Aristotle, *Physics* VI.2, 233a21-26.

Source: Aristotle, *Physics* VI.2, 233a21-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContinuumInfiniteByDivisionOrExtentReading
    (InfiniteByDivision InfiniteByExtent : Prop) : Prop :=
  InfiniteByDivision ∨ InfiniteByExtent

/-- What is quantitatively infinite by extent cannot be traversed in a finite time
in Aristotle, *Physics* VI.2, 233a26-30.

Source: Aristotle, *Physics* VI.2, 233a26-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ExtentInfiniteNotTraversableInFiniteTimeReading
    (ExtentInfiniteTraversableInFiniteTime : Prop) : Prop :=
  ¬ ExtentInfiniteTraversableInFiniteTime

/-- A continuum infinite by division can be traversed as a finite whole because the
corresponding time is itself infinite by division in Aristotle, *Physics* VI.2,
233a26-31.

Source: Aristotle, *Physics* VI.2, 233a26-31 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DivisionallyInfiniteTraversableInDivisionallyInfiniteTimeReading
    (DivisionallyInfiniteContinuumTraversableAsFiniteWhole
      CorrespondingTimeInfiniteByDivision : Prop) : Prop :=
  DivisionallyInfiniteContinuumTraversableAsFiniteWhole ∧
    CorrespondingTimeInfiniteByDivision

/-- Zeno's traversal argument falsely treats touching infinitely many divisional
parts as impossible in a finite whole time in Aristotle, *Physics* VI.2, 233a21-31.

Source: Aristotle, *Physics* VI.2, 233a21-31 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ZenoTraversalConflatesInfinitySensesReading
    (ZenoConflatesDivisionalInfinityWithInfiniteExtent : Prop) : Prop :=
  ZenoConflatesDivisionalInfinityWithInfiniteExtent

/-- Infinite traversal time and infinite magnitude imply one another in Aristotle,
*Physics* VI.2, 233a31-233b14; neither an infinite magnitude is traversed in finite
time nor a finite magnitude in infinite time.

Source: Aristotle, *Physics* VI.2, 233a31-233b14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteTraversalTimeIffInfiniteMagnitudeReading
    (TraversalTimeInfinite MagnitudeInfinite : Prop) : Prop :=
  TraversalTimeInfinite ↔ MagnitudeInfinite

/-- Equal finite portions of a finite magnitude are traversed in equal finite times
and measure the whole in finitely many steps in Aristotle, *Physics* VI.2,
233b1-14, excluding an infinite traversal time for that finite whole.

Source: Aristotle, *Physics* VI.2, 233b1-14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FinitePortionsMeasureFiniteWholeTraversalReading
    (FinitePortionsMeasureWhole EqualPortionsTakeEqualFiniteTimes
      WholeTraversalTimeFinite : Prop) : Prop :=
  (FinitePortionsMeasureWhole ∧ EqualPortionsTakeEqualFiniteTimes) →
    WholeTraversalTimeFinite

/-- In Aristotle's final ratio construction in *Physics* VI.2, 233b15-31, faster
and slower movers divide the same time in ratios of three and two, forcing a further
division of a supposedly indivisible magnitude-part.

Source: Aristotle, *Physics* VI.2, 233b15-31 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SpeedRatioDividesSupposedIndivisibleReading
    (FasterSlowerRatioConstruction DividesSupposedIndivisiblePart : Prop) : Prop :=
  FasterSlowerRatioConstruction ∧ DividesSupposedIndivisiblePart

/-- Aristotle's inferential transition in *Physics* VI.2, 233b15-32: if the
faster/slower ratio construction divides a supposedly indivisible part, no continuous
thing is partless.

Source: Aristotle, *Physics* VI.2, 233b15-32 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SpeedRatioDivisionImpliesNoContinuousPartlessReading
    (FasterSlowerRatioConstruction DividesSupposedIndivisiblePart
      NoContinuousThingPartless : Prop) : Prop :=
  (FasterSlowerRatioConstruction ∧ DividesSupposedIndivisiblePart) →
    NoContinuousThingPartless

/-- No continuous thing is partless in Aristotle, *Physics* VI.2, 233b15-32.

Source: Aristotle, *Physics* VI.2, 233b15-32 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoContinuousThingPartlessReading
    (NoContinuousThingPartless : Prop) : Prop :=
  NoContinuousThingPartless

end TruthCore.Greek.Aristotle.Physics
