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

end TruthCore.Greek.Aristotle.Physics
