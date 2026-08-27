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

/-- Temporal measurement of motion in Aristotle, *Physics* IV.12, 221a4-8: for a motion to
be in time is for both the motion and its being to be measured by time.

Source: Aristotle, *Physics* IV.12, 221a4-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionInTimeMeansMotionAndItsBeingMeasuredReading
    (MotionIsInTime MotionAndItsBeingMeasuredByTime : Prop) : Prop :=
  MotionIsInTime → MotionAndItsBeingMeasuredByTime

/-- Generalization of temporal measurement in Aristotle, *Physics* IV.12, 221a7-10: for
anything to be in time is for its being to be measured by time.

Source: Aristotle, *Physics* IV.12, 221a7-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BeingInTimeEntailsBeingMeasuredByTimeReading
    (ThingIsInTime ThingBeingMeasuredByTime : Prop) : Prop :=
  ThingIsInTime → ThingBeingMeasuredByTime

/-- Two proposed senses in Aristotle, *Physics* IV.12, 221a10-14: “in time” might mean
coexisting when time exists or being in time as something is in number; the subsequent
argument selects and refines the latter.

Source: Aristotle, *Physics* IV.12, 221a10-14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TwoCandidateSensesOfBeingInTimeReading
    (BeingInTimeMeansCoexistingWithTime BeingInTimeMeansBeingInNumber : Prop) : Prop :=
  BeingInTimeMeansCoexistingWithTime ∨ BeingInTimeMeansBeingInNumber

/-- Number analogy in Aristotle, *Physics* IV.12, 221a13-19: now, before, and after belong
to time as unit, odd, and even belong to number, while ordinary things are in time as
numbered things are in number.

Source: Aristotle, *Physics* IV.12, 221a13-19 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TemporalTermsBelongToTimeAndThingsAreNumberedByItReading
    (NowBeforeAfterBelongToTime ThingsInTimeAreNumberedByTime : Prop) : Prop :=
  NowBeforeAfterBelongToTime ∧ ThingsInTimeAreNumberedByTime

/-- Temporal containment in Aristotle, *Physics* IV.12, 221a18-20: things in time are
contained by time as things in number are contained by number and things in place by place.

Source: Aristotle, *Physics* IV.12, 221a18-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ThingsInTimeAreContainedByTimeReading
    (ThingIsInTime ThingIsContainedByTime : Prop) : Prop :=
  ThingIsInTime → ThingIsContainedByTime

/-- Rejection of mere coexistence in Aristotle, *Physics* IV.12, 221a19-26: being in time
cannot mean merely existing whenever time exists, since that would absurdly put any
coexistent thing in any other, such as the heaven in a grain.

Source: Aristotle, *Physics* IV.12, 221a19-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MereCoexistenceDoesNotEstablishBeingInTimeReading
    (ThingCoexistsWithTime ThingIsInTime : Prop) : Prop :=
  ThingCoexistsWithTime → ¬ ThingIsInTime

/-- Enclosing-time consequence in Aristotle, *Physics* IV.12, 221a26-30: for every thing
in time there is a greater time that contains it.

Source: Aristotle, *Physics* IV.12, 221a26-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EveryThingInTimeIsContainedByGreaterTimeReading
    (ThingIsInTime GreaterTimeContainsThing : Prop) : Prop :=
  ThingIsInTime → GreaterTimeContainsThing

/-- Temporal affection in Aristotle, *Physics* IV.12, 221a30-221b3: things in time waste,
age, and are forgotten through time, whereas time is not ordinarily said to make them learn,
young, or beautiful.

Source: Aristotle, *Physics* IV.12, 221a30-221b3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeAssociatedWithDecayNotImprovementReading
    (TimeWastesAgesAndBringsForgetting
      TimeMakesThingsLearnYoungOrBeautiful : Prop) : Prop :=
  TimeWastesAgesAndBringsForgetting ∧
    ¬ TimeMakesThingsLearnYoungOrBeautiful

/-- Aristotle's causal explanation in *Physics* IV.12, 221b1-3: time is chiefly a cause of
destruction because it numbers motion and motion displaces an existing condition.

Source: Aristotle, *Physics* IV.12, 221b1-3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeChieflyCausesDestructionThroughMotionReading
    (TimeNumbersMotion MotionDisplacesExistingCondition
      TimeChieflyCausesDestruction : Prop) : Prop :=
  TimeNumbersMotion ∧ MotionDisplacesExistingCondition →
    TimeChieflyCausesDestruction

/-- Measurement exclusion for eternal things in Aristotle, *Physics* IV.12, 221b3-8:
eternal things qua eternal are neither measured nor affected by time.

Source: Aristotle, *Physics* IV.12, 221b3-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EternalThingNotMeasuredOrAffectedByTimeReading
    (ThingIsEternalQuaEternal ThingBeingMeasuredByTime
      ThingAffectedByTime : Prop) : Prop :=
  ThingIsEternalQuaEternal →
    ¬ ThingBeingMeasuredByTime ∧ ¬ ThingAffectedByTime

/-- Conclusion about eternal things in Aristotle, *Physics* IV.12, 221b3-8: eternal things
qua eternal are not in time.

Source: Aristotle, *Physics* IV.12, 221b3-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EternalThingNotInTimeReading
    (ThingIsEternalQuaEternal ThingIsInTime : Prop) : Prop :=
  ThingIsEternalQuaEternal → ¬ ThingIsInTime

end TruthCore.Greek.Aristotle.Physics
