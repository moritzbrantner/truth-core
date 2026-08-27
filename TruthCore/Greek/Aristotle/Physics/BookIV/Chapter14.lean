import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter13

namespace TruthCore.Greek.Aristotle.Physics

/-- Universal speed comparison in Aristotle, *Physics* IV.14, 222b30-223a1: faster and
slower are found with respect to every kind of change.

Source: Aristotle, *Physics* IV.14, 222b30-223a1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EveryChangeAdmitsFasterAndSlowerReading
    (EveryChangeAdmitsFasterAndSlower : Prop) : Prop :=
  EveryChangeAdmitsFasterAndSlower

/-- Faster change in Aristotle, *Physics* IV.14, 223a1-4: under comparison over the same
interval and with uniform motion, the faster is what reaches the relevant condition first.

Source: Aristotle, *Physics* IV.14, 223a1-4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FasterChangeReachesConditionEarlierReading
    (ChangesOverSameInterval ChangesAreUniform OneReachesConditionEarlier
      OneChangesFaster : Prop) : Prop :=
  ChangesOverSameInterval ∧ ChangesAreUniform ∧ OneReachesConditionEarlier →
    OneChangesFaster

/-- Temporal location of before and after in Aristotle, *Physics* IV.14, 223a4-9: they are
defined by distance from the now, and because the now and its distance are in time, before
and after are in time.

Source: Aristotle, *Physics* IV.14, 223a4-9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BeforeAfterAreInTimeByDistanceFromNowReading
    (BeforeAfterAreDistancesFromNow NowIsInTime DistancesFromNowAreInTime
      BeforeAfterAreInTime : Prop) : Prop :=
  BeforeAfterAreDistancesFromNow ∧ NowIsInTime ∧ DistancesFromNowAreInTime →
    BeforeAfterAreInTime

/-- Reversed temporal ordering in Aristotle, *Physics* IV.14, 223a9-13: in the past the
earlier is farther from the now and the later nearer, while in the future the earlier is
nearer and the later farther.

Source: Aristotle, *Physics* IV.14, 223a9-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PastFutureBeforeAfterOrderingReversedReading
    (PastBeforeFartherFromNow PastAfterNearerNow FutureBeforeNearerNow
      FutureAfterFartherFromNow : Prop) : Prop :=
  PastBeforeFartherFromNow ∧ PastAfterNearerNow ∧ FutureBeforeNearerNow ∧
    FutureAfterFartherFromNow

/-- Universal conclusion in Aristotle, *Physics* IV.14, 223a13-15: because before is in
time and accompanies every motion, every change and every motion is in time.

Source: Aristotle, *Physics* IV.14, 223a13-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EveryChangeAndMotionIsInTimeReading
    (EveryChangeIsInTime EveryMotionIsInTime : Prop) : Prop :=
  EveryChangeIsInTime ∧ EveryMotionIsInTime

/-- Time's apparent ubiquity in Aristotle, *Physics* IV.14, 223a16-21: time belongs to
motion as its number, all terrestrial and celestial things are movable and in place, and
time and motion therefore accompany one another potentially and actually.

Source: Aristotle, *Physics* IV.14, 223a16-21 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeAppearsEverywhereThroughUniversalMovabilityReading
    (TimeIsNumberBelongingToMotion AllTerrestrialAndCelestialThingsAreMovable
      AllSuchThingsAreInPlace TimeAndMotionTogetherPotentiallyAndActually
      TimeAppearsEverywhere : Prop) : Prop :=
  TimeIsNumberBelongingToMotion ∧ AllTerrestrialAndCelestialThingsAreMovable ∧
    AllSuchThingsAreInPlace →
      TimeAndMotionTogetherPotentiallyAndActually ∧ TimeAppearsEverywhere

/-- Counter requirement in Aristotle, *Physics* IV.14, 223a21-25: what is counted or
countable, and hence number in the relevant sense, requires the possibility of a counter.

Source: Aristotle, *Physics* IV.14, 223a21-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CountedOrCountableNumberRequiresCounterReading
    (CountedOrCountableNumberExists CounterExists : Prop) : Prop :=
  ¬ CounterExists → ¬ CountedOrCountableNumberExists

/-- Counting capacity in Aristotle, *Physics* IV.14, 223a25-26: nothing except soul, and
specifically intellect in soul, is naturally capable of counting.

Source: Aristotle, *Physics* IV.14, 223a25-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def OnlySoulIntellectCanCountReading
    (CounterExists SoulOrIntellectInSoulExists : Prop) : Prop :=
  ¬ SoulOrIntellectInSoulExists → ¬ CounterExists

/-- Qualified dependence of time on soul in Aristotle, *Physics* IV.14, 223a21-29: without
soul or intellect in soul there is no time insofar as time is counted or countable number.

Source: Aristotle, *Physics* IV.14, 223a21-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def WithoutSoulNoTimeAsNumberReading
    (TimeExistsAsCountedOrCountableNumber SoulOrIntellectInSoulExists : Prop) : Prop :=
  ¬ SoulOrIntellectInSoulExists → ¬ TimeExistsAsCountedOrCountableNumber

/-- Aristotle's exception in *Physics* IV.14, 223a26-29: without soul, the motion that
underlies time may still exist, with before and after in motion, though not as numbered time.

Source: Aristotle, *Physics* IV.14, 223a26-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionSubstrateMayExistWithoutSoulReading
    (MotionCanExistWithoutSoul BeforeAfterBelongToMotion
      TimeIsBeforeAfterQuaCountable : Prop) : Prop :=
  MotionCanExistWithoutSoul ∧ BeforeAfterBelongToMotion ∧
    TimeIsBeforeAfterQuaCountable

/-- Scope of time's numbering in Aristotle, *Physics* IV.14, 223a30-223b1: time is number
of every kind of motion precisely qua motion, and thus number of continuous motion in
general rather than of one particular kind.

Source: Aristotle, *Physics* IV.14, 223a30-223b1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeNumbersContinuousMotionGenerallyReading
    (TimeNumbersEveryMotionQuaMotion TimeNumbersContinuousMotionGenerally
      TimeNumbersOnlyOneParticularMotionKind : Prop) : Prop :=
  TimeNumbersEveryMotionQuaMotion ∧ TimeNumbersContinuousMotionGenerally ∧
    ¬ TimeNumbersOnlyOneParticularMotionKind

/-- Numerical identity of time in Aristotle, *Physics* IV.14, 223b1-5: equal and
simultaneous temporal number is one and the same time, while nonsimultaneous equal times
remain one in kind.

Source: Aristotle, *Physics* IV.14, 223b1-5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EqualSimultaneousNumberIsOneSameTimeReading
    (TemporalNumbersAreEqual TemporalNumbersAreSimultaneous TimeIsOneAndSame : Prop) : Prop :=
  TemporalNumbersAreEqual ∧ TemporalNumbersAreSimultaneous → TimeIsOneAndSame

/-- Simultaneous different motions in Aristotle, *Physics* IV.14, 223b5-10: motions that
end together can differ in speed and kind while their temporal number remains equal and
simultaneous.

Source: Aristotle, *Physics* IV.14, 223b5-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DistinctMotionsCanHaveEqualSimultaneousNumberReading
    (MotionsAreDistinct TemporalNumbersAreEqual TemporalNumbersAreSimultaneous : Prop) : Prop :=
  MotionsAreDistinct → TemporalNumbersAreEqual ∧ TemporalNumbersAreSimultaneous

/-- Shared time of distinct motions in Aristotle, *Physics* IV.14, 223b5-13: simultaneous
motions may be separate and unlike, yet share one and the same time.

Source: Aristotle, *Physics* IV.14, 223b5-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DistinctSimultaneousMotionsShareSameTimeReading
    (MotionsAreDistinct MotionsShareOneSameTime : Prop) : Prop :=
  MotionsAreDistinct → MotionsShareOneSameTime

/-- Explanation of time's sameness in Aristotle, *Physics* IV.14, 223b10-13: motions are
different and separate, while time is everywhere the same because the number of equal and
simultaneous motions is one and the same.

Source: Aristotle, *Physics* IV.14, 223b10-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DistinctMotionsSameTimeThroughEqualSimultaneousNumberReading
    (MotionsDifferentAndSeparate EqualSimultaneousNumberOneAndSame
      TimeEverywhereSame : Prop) : Prop :=
  MotionsDifferentAndSeparate ∧ EqualSimultaneousNumberOneAndSame →
    TimeEverywhereSame

/-- Homogeneous-unit measurement in Aristotle, *Physics* IV.14, 223b13-18: each thing is
numbered by one thing homogeneous with it, and time is measured by a determinate time.

Source: Aristotle, *Physics* IV.14, 223b13-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def HomogeneousUnitAndDeterminateTimeMeasureReading
    (EachThingMeasuredByHomogeneousUnit TimeMeasuredByDeterminateTime : Prop) : Prop :=
  EachThingMeasuredByHomogeneousUnit ∧ TimeMeasuredByDeterminateTime

/-- Primary temporal measure in Aristotle, *Physics* IV.14, 223b18-20: regular circular
motion is the foremost measure because its number is best known.

Source: Aristotle, *Physics* IV.14, 223b18-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RegularCircularMotionIsPrimaryMeasureReading
    (RegularCircularMotionNumberBestKnown RegularCircularMotionPrimaryMeasure : Prop) : Prop :=
  RegularCircularMotionNumberBestKnown → RegularCircularMotionPrimaryMeasure

/-- Uniformity contrast in Aristotle, *Physics* IV.14, 223b20-23: alteration, growth, and
generation are not uniform, whereas locomotion can be uniform.

Source: Aristotle, *Physics* IV.14, 223b20-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def OnlyLocomotionAmongListedChangesCanBeUniformReading
    (AlterationUniform GrowthUniform GenerationUniform LocomotionCanBeUniform : Prop) : Prop :=
  ¬ AlterationUniform ∧ ¬ GrowthUniform ∧ ¬ GenerationUniform ∧
    LocomotionCanBeUniform

/-- Source of the sphere-motion identification in Aristotle, *Physics* IV.14, 223b23-25:
time is thought to be the sphere's motion because that motion measures both other motions
and time. This records the explanation of the appearance, not an identity claim.

Source: Aristotle, *Physics* IV.14, 223b23-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SphereMotionMeasurementExplainsTimeIdentificationReading
    (SphereMotionMeasuresOtherMotions SphereMotionMeasuresTime
      TimeThoughtIdenticalToSphereMotion : Prop) : Prop :=
  SphereMotionMeasuresOtherMotions ∧ SphereMotionMeasuresTime →
    TimeThoughtIdenticalToSphereMotion

/-- Circular measurement premise in Aristotle, *Physics* IV.14, 223b23-224a2: time is
measured by regular circular motion.

Source: Aristotle, *Physics* IV.14, 223b23-224a2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CircularMotionMeasuresTimeReading
    (TimeMeasuredByCircularMotion : Prop) : Prop :=
  TimeMeasuredByCircularMotion

/-- Appearance principle in Aristotle, *Physics* IV.14, 223b25-224a2: time's being
measured by circular motion explains why time and temporally judged affairs appear cyclical.

Source: Aristotle, *Physics* IV.14, 223b25-224a2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CircularMeasurementMakesTimeAppearCircularReading
    (TimeMeasuredByCircularMotion TimeAppearsCircular : Prop) : Prop :=
  TimeMeasuredByCircularMotion → TimeAppearsCircular

/-- Qualified appearance conclusion in Aristotle, *Physics* IV.14, 223b25-224a2: time
appears circular.

Source: Aristotle, *Physics* IV.14, 223b25-224a2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeAppearsCircularReading (TimeAppearsCircular : Prop) : Prop :=
  TimeAppearsCircular

/-- Cyclical-affairs explanation in Aristotle, *Physics* IV.14, 223b25-224a2: human and
natural affairs are called a circle because time judges their beginnings and ends as by a
period, while time itself appears circular through circular measurement.

Source: Aristotle, *Physics* IV.14, 223b25-224a2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CyclicalAffairsAppearanceComesFromCircularTimeMeasureReading
    (AffairsJudgedByTime HavePeriodicBeginningsAndEnds
      TimeMeasuredByCircularMotion AffairsAppearCyclical : Prop) : Prop :=
  AffairsJudgedByTime ∧ HavePeriodicBeginningsAndEnds ∧
    TimeMeasuredByCircularMotion → AffairsAppearCyclical

/-- Qualified sameness in Aristotle, *Physics* IV.14, 224a2-16: equal groups of different
subjects have the same number but not the same decad or the same ten, just as equilateral
and scalene triangles are the same figure but not the same triangle.

Source: Aristotle, *Physics* IV.14, 224a2-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SameNumberButDifferentEnumeratedWholeReading
    (DifferentSubjectGroupsHaveSameNumber SameEnumeratedDecad
      DifferentTrianglesSameFigure SameTriangle : Prop) : Prop :=
  DifferentSubjectGroupsHaveSameNumber ∧ ¬ SameEnumeratedDecad ∧
    DifferentTrianglesSameFigure ∧ ¬ SameTriangle

end TruthCore.Greek.Aristotle.Physics
