import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter7

namespace TruthCore.Greek.Aristotle.Physics

/-- What is coming to rest is still moving while it comes to rest, since if it were
not moving it would already be at rest and a resting thing cannot still be coming
to rest, in Aristotle, *Physics* VI.8, 238b23-25.

Source: Aristotle, *Physics* VI.8, 238b23-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ComingToRestRemainsMotionReading
    (ThingIsComingToRest ThingIsMoving : Prop) : Prop :=
  ThingIsComingToRest → ThingIsMoving

/-- Coming to rest necessarily occurs in time because it is motion, and its being
faster or slower is itself temporally assessed, in Aristotle, *Physics* VI.8,
238b25-30.

Source: Aristotle, *Physics* VI.8, 238b25-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ComingToRestOccursInTimeReading
    (ThingIsComingToRest ComingToRestOccursInTime : Prop) : Prop :=
  ThingIsComingToRest → ComingToRestOccursInTime

/-- A thing coming to rest in its primary cessation time is coming to rest in every
arbitrary subinterval of that time in Aristotle, *Physics* VI.8, 238b30-35.

Source: Aristotle, *Physics* VI.8, 238b30-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ComingToRestInEveryPrimarySubintervalReading
    (WholeTimeIsPrimary CessationInArbitrarySubinterval : Prop) : Prop :=
  WholeTimeIsPrimary → CessationInArbitrarySubinterval

/-- Any proposed first interval of coming to rest is self-defeating: it cannot be
indivisible because cessation is motion, and if divisible the thing is already
coming to rest in each subinterval, in Aristotle, *Physics* VI.8, 239a1-10.

Source: Aristotle, *Physics* VI.8, 239a1-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ProposedFirstCessationIntervalNotFirstReading
    (ProposedFirstCessationInterval : Prop) : Prop :=
  ProposedFirstCessationInterval → ¬ ProposedFirstCessationInterval

/-- There is no first extended interval in which coming to rest begins in Aristotle,
*Physics* VI.8, 239a1-10.

Source: Aristotle, *Physics* VI.8, 239a1-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoFirstCessationIntervalReading
    (FirstCessationIntervalExists : Prop) : Prop :=
  ¬ FirstCessationIntervalExists

/-- Rest is judged by sameness of state now and before, requiring at least two nows
rather than one indivisible instant, in Aristotle, *Physics* VI.8, 239a10-16.

Source: Aristotle, *Physics* VI.8, 239a10-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RestRequiresSamenessAcrossSuccessiveNowsReading
    (ThingIsAtRest SameStateNowAndBefore : Prop) : Prop :=
  ThingIsAtRest → SameStateNowAndBefore

/-- If an interval of rest is divisible, the thing rests in every arbitrary part of
it, so no divisible interval can be the first interval of rest, in Aristotle,
*Physics* VI.8, 239a16-20.

Source: Aristotle, *Physics* VI.8, 239a16-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DivisibleRestIntervalHasRestInEveryPartReading
    (RestIntervalDivisible RestsInEveryArbitraryPart : Prop) : Prop :=
  RestIntervalDivisible → RestsInEveryArbitraryPart

/-- No time, magnitude, or continuum has a first extended part, because every such
continuum is infinitely divisible, in Aristotle, *Physics* VI.8, 239a20-22.

Source: Aristotle, *Physics* VI.8, 239a20-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoFirstExtendedPartOfContinuumReading
    (TimeHasNoFirstExtendedPart MagnitudeHasNoFirstExtendedPart
      EveryContinuumHasNoFirstExtendedPart : Prop) : Prop :=
  TimeHasNoFirstExtendedPart ∧ MagnitudeHasNoFirstExtendedPart ∧
    EveryContinuumHasNoFirstExtendedPart

/-- Rest requires the whole subject and each of its parts to remain in the same
determinate state through a time, so that the same attribution is true at successive
nows, in Aristotle, *Physics* VI.8, 239a25-28.

Source: Aristotle, *Physics* VI.8, 239a25-28 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RestRequiresWholeAndPartsSameThroughTimeReading
    (ThingIsAtRest WholeAndPartsSameThroughTime : Prop) : Prop :=
  ThingIsAtRest → WholeAndPartsSameThroughTime

/-- If a subject were wholly in the same determinate state through a time, it would
be at rest in that state in Aristotle, *Physics* VI.8, 239a25-30.

Source: Aristotle, *Physics* VI.8, 239a25-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def WhollyDeterminateThroughTimeEntailsRestReading
    (WhollyDeterminateThroughTime ThingIsAtRest : Prop) : Prop :=
  WhollyDeterminateThroughTime → ThingIsAtRest

/-- A thing moving in its primary motion-time cannot be at rest during that time in
Aristotle, *Physics* VI.8, 239b2-4.

Source: Aristotle, *Physics* VI.8, 239b2-4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PrimaryMotionExcludesRestDuringTimeReading
    (MovesInPrimaryTime ThingIsAtRestDuringThatTime : Prop) : Prop :=
  MovesInPrimaryTime → ¬ ThingIsAtRestDuringThatTime

/-- During the primary time of its motion, a moving thing cannot be wholly in one
determinate state through any temporal part, since that would make it rest, in
Aristotle, *Physics* VI.8, 239a23-239b4.

Source: Aristotle, *Physics* VI.8, 239a23-239b4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MovingThingNotWhollyDeterminateDuringPrimaryTimeReading
    (MovesInPrimaryTime WhollyDeterminateThroughTime : Prop) : Prop :=
  MovesInPrimaryTime → ¬ WhollyDeterminateThroughTime

/-- A moving thing may be at a determinate boundary-state in a now, but this occurs
at the limit of time and does not constitute rest through time, in Aristotle,
*Physics* VI.8, 239a30-239b2.

Source: Aristotle, *Physics* VI.8, 239a30-239b2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DeterminateAtNowIsBoundaryNotRestReading
    (AtDeterminateStateInNow AtBoundaryOfTime NotRestingThere : Prop) : Prop :=
  AtDeterminateStateInNow → AtBoundaryOfTime ∧ NotRestingThere

/-- Neither motion nor rest occurs in a now, although it may be true in that now
that the subject is not moving and is at a determinate state, in Aristotle,
*Physics* VI.8, 239a35-239b2.

Source: Aristotle, *Physics* VI.8, 239a35-239b2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NeitherMotionNorRestOccursInNowReading
    (MotionOccursInNow RestOccursInNow NonmotionTrueInNow
      DeterminateStateTrueInNow : Prop) : Prop :=
  ¬ MotionOccursInNow ∧ ¬ RestOccursInNow ∧ NonmotionTrueInNow ∧
    DeterminateStateTrueInNow

end TruthCore.Greek.Aristotle.Physics
