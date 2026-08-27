import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter12

namespace TruthCore.Greek.Aristotle.Physics

/-- The now as temporal joint and limit in Aristotle, *Physics* IV.13, 222a10-14: it
connects past and future time while serving as the end of the former and beginning of the
latter.

Source: Aristotle, *Physics* IV.13, 222a10-14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NowConnectsAndLimitsPastAndFutureReading
    (NowConnectsPastAndFuture NowEndsPast NowBeginsFuture : Prop) : Prop :=
  NowConnectsPastAndFuture ∧ NowEndsPast ∧ NowBeginsFuture

/-- The now's two roles in Aristotle, *Physics* IV.13, 222a14-18: as a potential divider it
is always different, while as what binds time together it is always the same.

Source: Aristotle, *Physics* IV.13, 222a14-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NowDifferentAsDividerSameAsConnectorReading
    (NowDividesTimePotentially NowAlwaysDifferentAsDivider NowAlwaysSameAsConnector : Prop) : Prop :=
  NowDividesTimePotentially ∧ NowAlwaysDifferentAsDivider ∧ NowAlwaysSameAsConnector

/-- Qualified identity of division and union in Aristotle, *Physics* IV.13, 222a18-20: the
now's dividing and unifying roles belong to the same thing in the same respect, but their
being or account is not the same.

Source: Aristotle, *Physics* IV.13, 222a18-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NowDivisionUnitySameSubjectDifferentBeingReading
    (DivisionAndUnitySameSubjectAndRespect DivisionAndUnitySameInBeing : Prop) : Prop :=
  DivisionAndUnitySameSubjectAndRespect ∧ ¬ DivisionAndUnitySameInBeing

/-- Proximity sense of “now” in Aristotle, *Physics* IV.13, 222a20-24: an event in time
near the present now may be called now, while remote events such as the Trojan events or
the flood are not called now merely because time is continuous with them.

Source: Aristotle, *Physics* IV.13, 222a20-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DerivativeNowTracksTemporalProximityReading
    (EventTimeIsNearPresent EventSaidToOccurNow RemoteEventSaidToOccurNow : Prop) : Prop :=
  (EventTimeIsNearPresent → EventSaidToOccurNow) ∧ ¬ RemoteEventSaidToOccurNow

/-- The expression “sometime” in Aristotle, *Physics* IV.13, 222a24-28: it marks a
determinate time bounded relative to a now, with some finite temporal quantity between the
event and that now.

Source: Aristotle, *Physics* IV.13, 222a24-28 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SometimeIsDeterminateFiniteTimeRelativeToNowReading
    (SometimeIsDeterminateRelativeToNow IntervalFromNowIsFinite : Prop) : Prop :=
  SometimeIsDeterminateRelativeToNow ∧ IntervalFromNowIsFinite

/-- First recurrence conditional in Aristotle, *Physics* IV.13, 222a28-222b1: if one and
the same motion recurs, one and the same time recurs with it.

Source: Aristotle, *Physics* IV.13, 222a28-222b1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SameRecurringMotionEntailsSameRecurringTimeReading
    (SameMotionRecurs SameTimeRecurs : Prop) : Prop :=
  SameMotionRecurs → SameTimeRecurs

/-- Converse recurrence conditional in Aristotle, *Physics* IV.13, 222a28-222b1: if the
motion does not recur as one and the same, neither does the time.

Source: Aristotle, *Physics* IV.13, 222a28-222b1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DifferentRecurringMotionEntailsDifferentRecurringTimeReading
    (SameMotionRecurs SameTimeRecurs : Prop) : Prop :=
  ¬ SameMotionRecurs → ¬ SameTimeRecurs

/-- Paired recurrence conditionals in Aristotle, *Physics* IV.13, 222a28-222b1: recurrence
of the same motion brings recurrence of the same time, while failure of the former brings
failure of the latter.

Source: Aristotle, *Physics* IV.13, 222a28-222b1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionTimeRecurrenceCovariesReading
    (SameMotionRecurs SameTimeRecurs : Prop) : Prop :=
  (SameMotionRecurs → SameTimeRecurs) ∧ (¬ SameMotionRecurs → ¬ SameTimeRecurs)

/-- Qualified non-exhaustion of time in Aristotle, *Physics* IV.13, 222b1-7: the now ends
the past and begins a distinct future time, so time is always at a beginning and, given
everlasting motion, does not run out.

Source: Aristotle, *Physics* IV.13, 222b1-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NowBeginsDistinctFutureAndTimeDoesNotFailReading
    (NowEndsPast NowBeginsFuture PastAndFutureAreDistinct TimeIsAlwaysAtBeginning
      MotionAlwaysExists TimeFails : Prop) : Prop :=
  NowEndsPast ∧ NowBeginsFuture ∧ PastAndFutureAreDistinct ∧
    TimeIsAlwaysAtBeginning ∧ (MotionAlwaysExists → ¬ TimeFails)

/-- Nearness expressions in Aristotle, *Physics* IV.13, 222b7-18: “already” ranges over
the indivisibly near future and nearby past, “just now” marks the nearby past, and “long
ago” marks what is remote from the present now.

Source: Aristotle, *Physics* IV.13, 222b7-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AlreadyJustNowAndLongAgoTemporalProximityReading
    (AlreadyMarksIndivisiblyNearFuture AlreadyMarksNearbyPast
      JustNowMarksNearbyPast LongAgoMarksRemotePast : Prop) : Prop :=
  AlreadyMarksIndivisiblyNearFuture ∧ AlreadyMarksNearbyPast ∧
    JustNowMarksNearbyPast ∧ LongAgoMarksRemotePast

/-- Sudden change in Aristotle, *Physics* IV.13, 222b18-21: what occurs suddenly departs
from its prior condition within a time imperceptible because of its smallness.

Source: Aristotle, *Physics* IV.13, 222b18-21 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SuddenChangeOccursInImperceptiblyBriefTimeReading
    (ChangeOccursSuddenly ChangeDepartsPriorCondition
      ChangeOccursInImperceptiblyBriefTime : Prop) : Prop :=
  ChangeOccursSuddenly →
    ChangeDepartsPriorCondition ∧ ChangeOccursInImperceptiblyBriefTime

/-- Destructive asymmetry in Aristotle, *Physics* IV.13, 222b21-27: although generation
and corruption occur in time, change is intrinsically displacing, so time is associated
with destruction per se more than with generation, and with generation only incidentally.

Source: Aristotle, *Physics* IV.13, 222b21-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimePerSeDestructiveIncidentallyGenerativeReading
    (GenerationAndCorruptionOccurInTime ChangeIsIntrinsicallyDisplacing
      TimeIsPerSeCauseOfDestruction TimeIsPerSeCauseOfGeneration : Prop) : Prop :=
  GenerationAndCorruptionOccurInTime ∧ ChangeIsIntrinsicallyDisplacing →
    TimeIsPerSeCauseOfDestruction ∧ ¬ TimeIsPerSeCauseOfGeneration

/-- Final causal qualification in Aristotle, *Physics* IV.13, 222b27-29: even the
destruction customarily attributed to time is not produced by time itself; that change
merely happens in time.

Source: Aristotle, *Physics* IV.13, 222b27-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeDoesNotProduceDestructionReading
    (DestructionOccursInTime TimeProducesDestruction : Prop) : Prop :=
  DestructionOccursInTime ∧ ¬ TimeProducesDestruction

end TruthCore.Greek.Aristotle.Physics
