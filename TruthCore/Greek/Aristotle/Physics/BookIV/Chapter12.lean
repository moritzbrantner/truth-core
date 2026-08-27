import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter11

namespace TruthCore.Greek.Aristotle.Physics

/-- Minimum distinction in Aristotle, *Physics* IV.12, 220a27-220b1: time has a minimum
with respect to number—one or two—but no minimum with respect to magnitude, just as every
line remains divisible.

Source: Aristotle, *Physics* IV.12, 220a27-220b1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeHasNumericalButNoMagnitudeMinimumReading
    (TimeHasMinimumByNumber TimeHasMinimumByMagnitude : Prop) : Prop :=
  TimeHasMinimumByNumber ∧ ¬ TimeHasMinimumByMagnitude

/-- Predicates of time in Aristotle, *Physics* IV.12, 220b1-5: as continuous, time is long
or short; as number, many or few; it is not fast or slow.

Source: Aristotle, *Physics* IV.12, 220b1-5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeLongShortManyFewNotFastSlowReading
    (TimeIsLongOrShort TimeIsManyOrFew TimeIsFastOrSlow : Prop) : Prop :=
  TimeIsLongOrShort ∧ TimeIsManyOrFew ∧ ¬ TimeIsFastOrSlow

/-- Sameness qualification in Aristotle, *Physics* IV.12, 220b5-10: time is the same
everywhere simultaneously but not the same before and after, because changes and nows differ
across succession.

Source: Aristotle, *Physics* IV.12, 220b5-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeSameEverywhereSimultaneouslyDifferentBeforeAfterReading
    (SimultaneousTimeSameEverywhere TimeSameBeforeAndAfter : Prop) : Prop :=
  SimultaneousTimeSameEverywhere ∧ ¬ TimeSameBeforeAndAfter

/-- Number and numbered things in Aristotle, *Physics* IV.12, 220b9-13: the number one
hundred is the same for horses and humans, while the things numbered remain different.

Source: Aristotle, *Physics* IV.12, 220b9-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SameNumberCanNumberDifferentThingsReading
    (SameNumberAppliesToHorsesAndHumans HorsesAndHumansAreSameThings : Prop) : Prop :=
  SameNumberAppliesToHorsesAndHumans ∧ ¬ HorsesAndHumansAreSameThings

/-- Recurrence in Aristotle, *Physics* IV.12, 220b13-15: as one and the same motion can
occur again and again, so can a time such as a year, spring, or autumn.

Source: Aristotle, *Physics* IV.12, 220b13-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionAndTimeCanRecurReading
    (SameMotionCanRecur SameTimePeriodCanRecur : Prop) : Prop :=
  SameMotionCanRecur ∧ SameTimePeriodCanRecur

/-- First measurement direction in Aristotle, *Physics* IV.12, 220b15-24: time measures
motion because it is the number of motion.

Source: Aristotle, *Physics* IV.12, 220b15-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeMeasuresMotionReading (TimeMeasuresMotion : Prop) : Prop :=
  TimeMeasuresMotion

/-- Second measurement direction in Aristotle, *Physics* IV.12, 220b15-24: motion measures
time, as a counted horse can serve as the unit by which the number of horses is known.

Source: Aristotle, *Physics* IV.12, 220b15-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionMeasuresTimeReading (MotionMeasuresTime : Prop) : Prop :=
  MotionMeasuresTime

/-- Reciprocal-measurement conclusion in Aristotle, *Physics* IV.12, 220b15-24: time and
motion measure and delimit one another.

Source: Aristotle, *Physics* IV.12, 220b15-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeAndMotionMeasureOneAnotherReading
    (TimeMeasuresMotion MotionMeasuresTime : Prop) : Prop :=
  TimeMeasuresMotion ∧ MotionMeasuresTime

/-- Quantity structure in Aristotle, *Physics* IV.12, 220b24-30: magnitude, motion, and
time are quantities, continuous, and divisible in an ordered dependence from magnitude to
motion to time.

Source: Aristotle, *Physics* IV.12, 220b24-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MagnitudeMotionTimeQuantitativeContinuousDivisibleReading
    (MagnitudeQuantitativeContinuousDivisible
      MotionQuantitativeContinuousDivisible
      TimeQuantitativeContinuousDivisible : Prop) : Prop :=
  MagnitudeQuantitativeContinuousDivisible →
    MotionQuantitativeContinuousDivisible ∧
      TimeQuantitativeContinuousDivisible

/-- Road-journey analogy in Aristotle, *Physics* IV.12, 220b28-32: magnitude and motion
measure one another, as a road is called long from a long journey and the journey long from
the road.

Source: Aristotle, *Physics* IV.12, 220b28-32 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MagnitudeAndMotionMeasureOneAnotherReading
    (MagnitudeMeasuresMotion MotionMeasuresMagnitude : Prop) : Prop :=
  MagnitudeMeasuresMotion ∧ MotionMeasuresMagnitude

/-- Unit-based measurement in Aristotle, *Physics* IV.12, 220b32-221a4: time measures a
whole motion by delimiting a motion that measures it, as a cubit delimits a magnitude that
measures a whole length.

Source: Aristotle, *Physics* IV.12, 220b32-221a4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeMeasuresWholeMotionByDelimitedUnitReading
    (TimeDelimitsUnitMotion UnitMotionMeasuresWholeMotion : Prop) : Prop :=
  TimeDelimitsUnitMotion → UnitMotionMeasuresWholeMotion

end TruthCore.Greek.Aristotle.Physics
