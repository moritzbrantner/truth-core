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

/-- Incidental measurement of rest in Aristotle, *Physics* IV.12, 221b8-10: because time
measures motion and every rest is in time, time also measures rest incidentally.

Source: Aristotle, *Physics* IV.12, 221b8-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeMeasuresRestIncidentallyReading
    (TimeMeasuresMotion EveryRestIsInTime TimeMeasuresRestIncidentally : Prop) : Prop :=
  TimeMeasuresMotion ∧ EveryRestIsInTime → TimeMeasuresRestIncidentally

/-- Non-entailment of motion in Aristotle, *Physics* IV.12, 221b10-13: unlike being in
motion, being in time does not require moving, since something resting can be within the
number of motion.

Source: Aristotle, *Physics* IV.12, 221b10-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BeingInTimeDoesNotEntailMovingReading
    (ThingIsInTime ThingMoves RestingThingCanBeInTime : Prop) : Prop :=
  ¬ (ThingIsInTime → ThingMoves) ∧ RestingThingCanBeInTime

/-- Necessary conditions for rest in Aristotle, *Physics* IV.12, 221b13-15: not everything
unmoved rests; what rests is deprived of motion while naturally capable of moving.

Source: Aristotle, *Physics* IV.12, 221b13-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RestEntailsPrivationInNaturallyMovableReading
    (ThingRests ThingLacksMotion ThingIsNaturallyMovable : Prop) : Prop :=
  ThingRests → ThingLacksMotion ∧ ThingIsNaturallyMovable

/-- Number and measurement in Aristotle, *Physics* IV.12, 221b15-18: to be in number is
for there to be a number of the thing and for its being to be measured by that number; if
it is in time, its being is accordingly measured by time.

Source: Aristotle, *Physics* IV.12, 221b15-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BeingInNumberEntailsNumberAndMeasurementReading
    (ThingIsInNumber ThingHasNumber ThingBeingMeasuredByNumber : Prop) : Prop :=
  ThingIsInNumber → ThingHasNumber ∧ ThingBeingMeasuredByNumber

/-- Qualified temporal measurement in Aristotle, *Physics* IV.12, 221b18-23: time measures
the moving and resting thing precisely insofar as it moves or rests, measuring how much
motion or rest it has rather than merely how much the thing is.

Source: Aristotle, *Physics* IV.12, 221b18-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeMeasuresMovingAndRestingQuaSuchReading
    (TimeMeasuresMovingThingQuaMoving TimeMeasuresRestingThingQuaResting
      TimeMeasuresMovingThingMerelyQuaQuantity : Prop) : Prop :=
  TimeMeasuresMovingThingQuaMoving ∧ TimeMeasuresRestingThingQuaResting ∧
    ¬ TimeMeasuresMovingThingMerelyQuaQuantity

/-- Motion-rest scope of temporal measurement in Aristotle, *Physics* IV.12, 221b18-27:
anything whose being is measured by time falls under motion or rest.

Source: Aristotle, *Physics* IV.12, 221b18-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TemporalMeasurementEntailsMovingOrRestingReading
    (ThingBeingMeasuredByTime ThingMoves ThingRests : Prop) : Prop :=
  ThingBeingMeasuredByTime → ThingMoves ∨ ThingRests

/-- Exclusion from time in Aristotle, *Physics* IV.12, 221b23-27: whatever neither moves
nor rests is not in time.

Source: Aristotle, *Physics* IV.12, 221b23-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NeitherMovingNorRestingNotInTimeReading
    (ThingMoves ThingRests ThingIsInTime : Prop) : Prop :=
  ¬ ThingMoves ∧ ¬ ThingRests → ¬ ThingIsInTime

/-- Restriction on nonbeing in Aristotle, *Physics* IV.12, 221b27-31: not every nonbeing
is in time; an impossible state such as the diagonal's being commensurable with the side is
excluded.

Source: Aristotle, *Physics* IV.12, 221b27-31 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NotEveryNonbeingIsInTimeReading
    (SomeNonbeingIsImpossible ImpossibleNonbeingIsInTime : Prop) : Prop :=
  SomeNonbeingIsImpossible ∧ ¬ ImpossibleNonbeingIsInTime

/-- Temporal scope restatement in Aristotle, *Physics* IV.12, 221b31-34: everything whose
being time measures has its being in moving or resting.

Source: Aristotle, *Physics* IV.12, 221b31-34 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeMeasuredBeingIsInMovingOrRestingReading
    (ThingBeingMeasuredByTime ThingBeingIsInMoving ThingBeingIsInResting : Prop) : Prop :=
  ThingBeingMeasuredByTime → ThingBeingIsInMoving ∨ ThingBeingIsInResting

/-- Temporal inclusion of changing things in Aristotle, *Physics* IV.12, 221b34-222a1:
generable and corruptible things, which at one time are and at another are not, are
necessarily in time and are exceeded by a time greater than their being.

Source: Aristotle, *Physics* IV.12, 221b34-222a1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GenerableCorruptibleThingsNecessarilyInTimeReading
    (ThingIsGenerable ThingIsCorruptible ThingIsSometimesAndSometimesNot
      ThingIsInTime GreaterTimeExceedsThingBeing : Prop) : Prop :=
  ThingIsGenerable ∧ ThingIsCorruptible ∧ ThingIsSometimesAndSometimesNot →
    ThingIsInTime ∧ GreaterTimeExceedsThingBeing

/-- Temporal containment of nonbeing in Aristotle, *Physics* IV.12, 221b35-222a4: a
nonbeing contained by time was or will be, according to the temporal direction or directions
in which time contains it.

Source: Aristotle, *Physics* IV.12, 221b35-222a4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TemporallyContainedNonbeingWasOrWillBeReading
    (NonbeingIsContainedByTime NonbeingWas NonbeingWillBe : Prop) : Prop :=
  NonbeingIsContainedByTime → NonbeingWas ∨ NonbeingWillBe

/-- Atemporal exclusion in Aristotle, *Physics* IV.12, 222a1-4: a nonbeing that time does
not contain in any direction neither was, is, nor will be.

Source: Aristotle, *Physics* IV.12, 222a1-4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TemporallyUncontainedNonbeingNeverWasIsOrWillBeReading
    (NonbeingIsUncontainedByTime NonbeingWas NonbeingIs NonbeingWillBe : Prop) : Prop :=
  NonbeingIsUncontainedByTime → ¬ NonbeingWas ∧ ¬ NonbeingIs ∧ ¬ NonbeingWillBe

/-- Modal-temporal contrast in Aristotle, *Physics* IV.12, 222a4-9: a nonbeing whose
opposite always is never falls in time, whereas things whose contrary is not always can be
and not be and undergo generation and corruption.

Source: Aristotle, *Physics* IV.12, 222a4-9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ImpossibleAndContingentNonbeingTemporalContrastReading
    (OppositeAlwaysExists ImpossibleNonbeingIsInTime ContraryNotAlwaysExists
      ThingCanBeAndNotBe ThingHasGenerationAndCorruption : Prop) : Prop :=
  (OppositeAlwaysExists → ¬ ImpossibleNonbeingIsInTime) ∧
    (ContraryNotAlwaysExists → ThingCanBeAndNotBe ∧ ThingHasGenerationAndCorruption)

end TruthCore.Greek.Aristotle.Physics
