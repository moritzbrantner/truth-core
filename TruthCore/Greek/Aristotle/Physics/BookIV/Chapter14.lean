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

end TruthCore.Greek.Aristotle.Physics
