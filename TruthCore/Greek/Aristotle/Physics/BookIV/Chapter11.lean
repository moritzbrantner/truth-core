import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter10

namespace TruthCore.Greek.Aristotle.Physics

/-- Perception contrast in Aristotle, *Physics* IV.11, 218b21-219a1: when change escapes
notice, earlier and later nows are joined and the interval does not seem to be time; when the
soul perceives and distinguishes change, it says that time has elapsed.

Source: Aristotle, *Physics* IV.11, 218b21-219a1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def UnnoticedAndPerceivedChangeAffectTimeAwarenessReading
    (UnnoticedChangeJoinsEarlierAndLaterNows
      UnnoticedIntervalSeemsTimeless
      PerceivedDistinguishedChangeMakesTimeApparent : Prop) : Prop :=
  UnnoticedChangeJoinsEarlierAndLaterNows ∧ UnnoticedIntervalSeemsTimeless ∧
    PerceivedDistinguishedChangeMakesTimeApparent

/-- Dependence conclusion in Aristotle, *Physics* IV.11, 218b21-219a1: time does not exist
without motion and change. This does not identify time with motion.

Source: Aristotle, *Physics* IV.11, 218b21-219a1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeCannotExistWithoutMotionReading (TimeExistsWithoutMotion : Prop) : Prop :=
  ¬ TimeExistsWithoutMotion

/-- Co-perception in Aristotle, *Physics* IV.11, 219a1-10: motion in the soul makes time
seem to have elapsed even in darkness, and whenever time seems to have elapsed some motion
also seems to have occurred.

Source: Aristotle, *Physics* IV.11, 219a1-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionAndTimeArePerceivedTogetherReading
    (PerceivedMotionAccompaniesPerceivedTime
      PerceivedTimeAccompaniesPerceivedMotion : Prop) : Prop :=
  PerceivedMotionAccompaniesPerceivedTime ∧
    PerceivedTimeAccompaniesPerceivedMotion

/-- Inferential bridge in Aristotle, *Physics* IV.11, 219a1-10: because time is not motion
but also is not independent of motion, it must be something belonging to motion.

Source: Aristotle, *Physics* IV.11, 219a1-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeNonidentityAndDependenceEntailBelongingToMotionReading
    (TimeIsMotion TimeExistsWithoutMotion TimeBelongsToMotion : Prop) : Prop :=
  (¬ TimeIsMotion ∧ ¬ TimeExistsWithoutMotion) → TimeBelongsToMotion

/-- Intermediate conclusion in Aristotle, *Physics* IV.11, 219a1-10: time is something
belonging to motion.

Source: Aristotle, *Physics* IV.11, 219a1-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeBelongsToMotionReading (TimeBelongsToMotion : Prop) : Prop :=
  TimeBelongsToMotion

/-- Continuity dependence in Aristotle, *Physics* IV.11, 219a10-14: motion follows
continuous magnitude and is continuous because magnitude is; time follows motion and is
correspondingly continuous.

Source: Aristotle, *Physics* IV.11, 219a10-14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MagnitudeMotionTimeContinuityDependenceReading
    (MagnitudeIsContinuous MotionFollowsMagnitude TimeFollowsMotion
      MotionIsContinuous TimeIsContinuous : Prop) : Prop :=
  MagnitudeIsContinuous ∧ MotionFollowsMagnitude ∧ TimeFollowsMotion →
    MotionIsContinuous ∧ TimeIsContinuous

/-- Before-after ordering in Aristotle, *Physics* IV.11, 219a14-22: before and after are
first in place by position, then in motion by correspondence with magnitude, and finally in
time because time follows motion.

Source: Aristotle, *Physics* IV.11, 219a14-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BeforeAfterPassesFromMagnitudeThroughMotionToTimeReading
    (BeforeAfterInMagnitude BeforeAfterInMotion BeforeAfterInTime : Prop) : Prop :=
  BeforeAfterInMagnitude → BeforeAfterInMotion ∧ BeforeAfterInTime

/-- Same-substratum distinction in Aristotle, *Physics* IV.11, 219a18-22: before and after
in motion are motion in their underlying subject, but their being or account differs from
motion.

Source: Aristotle, *Physics* IV.11, 219a18-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BeforeAfterInMotionSameSubstratumDifferentAccountReading
    (BeforeAfterSharesMotionSubstratum BeforeAfterAccountIsMotion : Prop) : Prop :=
  BeforeAfterSharesMotionSubstratum ∧ ¬ BeforeAfterAccountIsMotion

/-- Apprehension of time in Aristotle, *Physics* IV.11, 219a22-30: time is known when the
soul marks motion by a perceived before and after.

Source: Aristotle, *Physics* IV.11, 219a22-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeKnownByMarkingMotionBeforeAndAfterReading
    (SoulMarksMotionByBeforeAndAfter TimeIsApprehended : Prop) : Prop :=
  SoulMarksMotionByBeforeAndAfter → TimeIsApprehended

/-- Two-now delimitation in Aristotle, *Physics* IV.11, 219a25-219b1: when the soul judges
two distinct nows, one before and one after with an interval between them, it says that time
has elapsed; treating the now as one leaves no apparent time.

Source: Aristotle, *Physics* IV.11, 219a25-219b1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TwoDistinctNowsDelimitTimeReading
    (SoulDistinguishesTwoNowsAndInterval
      TimeAppearsBetweenDistinctNows OneUndifferentiatedNowAppearsTimeless : Prop) : Prop :=
  SoulDistinguishesTwoNowsAndInterval → TimeAppearsBetweenDistinctNows ∧
    OneUndifferentiatedNowAppearsTimeless

/-- Aristotle's definition in *Physics* IV.11, 219b1-5: time is number of motion according
to before and after—not motion itself, but motion insofar as it admits of enumeration.

Source: Aristotle, *Physics* IV.11, 219b1-5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeIsNumberOfMotionAccordingToBeforeAfterReading
    (TimeIsMotion TimeIsNumberOfMotionAccordingToBeforeAfter : Prop) : Prop :=
  ¬ TimeIsMotion ∧ TimeIsNumberOfMotionAccordingToBeforeAfter

/-- Measurement support for the definition in Aristotle, *Physics* IV.11, 219b3-6: number
discriminates more and less generally, while time discriminates more and less motion, so
time is a kind of number.

Source: Aristotle, *Physics* IV.11, 219b3-6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeMeasuresMoreAndLessMotionAsNumberReading
    (NumberDistinguishesMoreAndLess TimeDistinguishesMoreAndLessMotion
      TimeIsKindOfNumber : Prop) : Prop :=
  NumberDistinguishesMoreAndLess ∧ TimeDistinguishesMoreAndLessMotion →
    TimeIsKindOfNumber

/-- Counted-counting distinction in Aristotle, *Physics* IV.11, 219b6-9: “number” can mean
what is counted or countable, or that by which we count; time is what is counted, not the
number by which counting is performed.

Source: Aristotle, *Physics* IV.11, 219b6-9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeIsCountedNumberNotCountingNumberReading
    (TimeIsCountedOrCountableNumber TimeIsCountingNumber : Prop) : Prop :=
  TimeIsCountedOrCountableNumber ∧ ¬ TimeIsCountingNumber

/-- Succession and simultaneity in Aristotle, *Physics* IV.11, 219b9-12: motion and time
are each successively other, while all time taken simultaneously is the same.

Source: Aristotle, *Physics* IV.11, 219b9-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionAndTimeSuccessiveWhileSimultaneousTimeSameReading
    (MotionIsSuccessivelyDifferent TimeIsSuccessivelyDifferent
      SimultaneousTimeIsSame : Prop) : Prop :=
  MotionIsSuccessivelyDifferent ∧ TimeIsSuccessivelyDifferent ∧
    SimultaneousTimeIsSame

/-- Sameness-difference account of the now in Aristotle, *Physics* IV.11, 219b10-16: the
now is the same in its underlying subject but different in being as it occurs in successive
before-and-after positions.

Source: Aristotle, *Physics* IV.11, 219b10-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NowSameInSubstratumDifferentInBeingReading
    (NowHasSameSubstratum NowDiffersInBeingAcrossSuccession : Prop) : Prop :=
  NowHasSameSubstratum ∧ NowDiffersInBeingAcrossSuccession

/-- Moving-body analogy in Aristotle, *Physics* IV.11, 219b15-23: a point, stone, or
Coriscus remains the same underlying thing while differing in account by being now here and
now elsewhere.

Source: Aristotle, *Physics* IV.11, 219b15-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MovingBodySameThingDifferentByLocationReading
    (MovingBodyRemainsSameThing MovingBodyDiffersBySuccessiveLocation : Prop) : Prop :=
  MovingBodyRemainsSameThing ∧ MovingBodyDiffersBySuccessiveLocation

/-- Ordered analogy in Aristotle, *Physics* IV.11, 219b15-25: the now follows the moving
body as time follows motion, and the moving body makes before and after in motion knowable.

Source: Aristotle, *Physics* IV.11, 219b15-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NowFollowsMovingBodyAsTimeFollowsMotionReading
    (NowFollowsMovingBody TimeFollowsMotion
      MovingBodyMakesBeforeAfterKnowable : Prop) : Prop :=
  NowFollowsMovingBody ∧ TimeFollowsMotion ∧
    MovingBodyMakesBeforeAfterKnowable

/-- Epistemic role of the moving subject in Aristotle, *Physics* IV.11, 219b25-32: motion
and locomotion are chiefly known through the determinate thing that moves, because it is a
particular while motion is not.

Source: Aristotle, *Physics* IV.11, 219b25-32 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MovingThingMakesMotionKnowableReading
    (MovingThingIsDeterminateParticular MotionIsDeterminateParticular
      MovingThingMakesMotionKnowable : Prop) : Prop :=
  MovingThingIsDeterminateParticular ∧ ¬ MotionIsDeterminateParticular →
    MovingThingMakesMotionKnowable

/-- First dependence direction in Aristotle, *Physics* IV.11, 219b32-220a4: if time did
not exist, the now would not exist.

Source: Aristotle, *Physics* IV.11, 219b32-220a4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoTimeEntailsNoNowReading (TimeExists NowExists : Prop) : Prop :=
  ¬ TimeExists → ¬ NowExists

/-- Second dependence direction in Aristotle, *Physics* IV.11, 219b32-220a4: if the now
did not exist, time would not exist.

Source: Aristotle, *Physics* IV.11, 219b32-220a4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoNowEntailsNoTimeReading (TimeExists NowExists : Prop) : Prop :=
  ¬ NowExists → ¬ TimeExists

/-- Mutual-dependence conclusion in Aristotle, *Physics* IV.11, 219b32-220a4: time and the
now stand or fall together.

Source: Aristotle, *Physics* IV.11, 219b32-220a4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeAndNowMutuallyDependentReading (TimeExists NowExists : Prop) : Prop :=
  (¬ TimeExists → ¬ NowExists) ∧ (¬ NowExists → ¬ TimeExists)

/-- Number-unit analogy in Aristotle, *Physics* IV.11, 220a1-7: time is the number of
locomotion while the now corresponds to the moving body as a unit of that number.

Source: Aristotle, *Physics* IV.11, 220a1-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeNumbersMotionAndNowIsItsUnitReading
    (TimeIsNumberOfLocomotion NowCorrespondsToMovingBody
      NowIsUnitOfTimeNumber : Prop) : Prop :=
  TimeIsNumberOfLocomotion ∧ NowCorrespondsToMovingBody ∧
    NowIsUnitOfTimeNumber

/-- Continuity and division in Aristotle, *Physics* IV.11, 220a7-14: the now both makes
time continuous and divides it by delimiting the earlier and later motion.

Source: Aristotle, *Physics* IV.11, 220a7-14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NowMakesTimeContinuousAndDividesItReading
    (NowMakesTimeContinuous NowDividesTime
      NowDelimitsEarlierAndLaterMotion : Prop) : Prop :=
  NowMakesTimeContinuous ∧ NowDividesTime ∧
    NowDelimitsEarlierAndLaterMotion

/-- Point analogy and its limit in Aristotle, *Physics* IV.11, 220a11-20: a point both
joins and delimits a line, but treating one point as both end and beginning introduces a
stop; the now instead is always different because the moving thing continues to move.

Source: Aristotle, *Physics* IV.11, 220a11-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PointAnalogyDoesNotMakeNowAStationaryDoubleLimitReading
    (PointJoinsAndDelimitsLine OnePointAsEndAndBeginningIntroducesRest
      MovingNowIsAlwaysDifferent : Prop) : Prop :=
  PointJoinsAndDelimitsLine ∧ OnePointAsEndAndBeginningIntroducesRest ∧
    MovingNowIsAlwaysDifferent

/-- Non-part status of the now in Aristotle, *Physics* IV.11, 220a18-24: the now is not a
part of time, just as a division of motion is not a part of motion and a point is not a part
of a line.

Source: Aristotle, *Physics* IV.11, 220a18-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NowIsNotPartOfTimeReading
    (NowIsPartOfTime MotionDivisionIsPartOfMotion PointIsPartOfLine : Prop) : Prop :=
  ¬ NowIsPartOfTime ∧ ¬ MotionDivisionIsPartOfMotion ∧ ¬ PointIsPartOfLine

/-- Dual aspect of the now in Aristotle, *Physics* IV.11, 220a24-26: as a limit the now is
not time but belongs to it incidentally, while insofar as it counts it is number.

Source: Aristotle, *Physics* IV.11, 220a24-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NowAsLimitIsNotTimeButAsCountingIsNumberReading
    (NowAsLimitIsTime NowAsLimitBelongsIncidentallyToTime
      NowAsCountingIsNumber : Prop) : Prop :=
  ¬ NowAsLimitIsTime ∧ NowAsLimitBelongsIncidentallyToTime ∧
    NowAsCountingIsNumber

end TruthCore.Greek.Aristotle.Physics
