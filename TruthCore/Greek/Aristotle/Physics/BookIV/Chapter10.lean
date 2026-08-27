import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter9

namespace TruthCore.Greek.Aristotle.Physics

/-- Method for beginning the inquiry into time in Aristotle, *Physics* IV.10, 217b29-32:
first work through the puzzles about whether time exists, and then ask what its nature is.

Source: Aristotle, *Physics* IV.10, 217b29-32 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeInquiryBeginsFromExistencePuzzlesReading
    (InvestigateWhetherTimeExistsBeforeItsNature : Prop) : Prop :=
  InvestigateWhetherTimeExistsBeforeItsNature

/-- Initial existence puzzle in Aristotle, *Physics* IV.10, 217b32-218a3: time may seem not
to exist, or to exist only obscurely, because its past no longer is and its future is not yet,
while time is composed from these.

Source: Aristotle, *Physics* IV.10, 217b32-218a3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PastFutureNonbeingMakesTimeExistencePuzzlingReading
    (PastNoLongerExists FutureDoesNotYetExist
      TimeComposedFromPastAndFuture TimeExistenceIsPuzzling : Prop) : Prop :=
  PastNoLongerExists ∧ FutureDoesNotYetExist ∧
    TimeComposedFromPastAndFuture → TimeExistenceIsPuzzling

/-- Parts puzzle in Aristotle, *Physics* IV.10, 218a3-8: a divisible existent should have
some or all of its parts existing, but time's past and future do not exist and the now is not
a part from which time is composed.

Source: Aristotle, *Physics* IV.10, 218a3-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimePartsDoNotMeetDivisibleExistenceConditionReading
    (DivisibleExistingWholeHasExistingParts PastAndFutureExist
      NowIsPartOfTime TimeComposedOfNows : Prop) : Prop :=
  DivisibleExistingWholeHasExistingParts ∧ ¬ PastAndFutureExist ∧
    ¬ NowIsPartOfTime ∧ ¬ TimeComposedOfNows

/-- Successive-now puzzle in Aristotle, *Physics* IV.10, 218a8-21: if each now is
different, an earlier now can perish neither in itself nor in a later, non-adjacent now,
without absurdly coexisting with the infinitely many intervening nows.

Source: Aristotle, *Physics* IV.10, 218a8-21 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SuccessiveNowsCannotPerishCoherentlyReading
    (EarlierNowPerishesInItself EarlierNowPerishesInLaterNow
      EarlierNowCoexistsWithInterveningNows : Prop) : Prop :=
  ¬ EarlierNowPerishesInItself ∧ ¬ EarlierNowPerishesInLaterNow ∧
    ¬ EarlierNowCoexistsWithInterveningNows

/-- Persistent-now puzzle in Aristotle, *Physics* IV.10, 218a21-30: one now cannot persist
through all time because finite divisible things have distinct limits, and putting earlier
and later events in one now would make them simultaneous.

Source: Aristotle, *Physics* IV.10, 218a21-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def OnePersistentNowCollapsesTemporalOrderReading
    (OneNowPersistsThroughAllTime EarlierAndLaterEventsBecomeSimultaneous : Prop) : Prop :=
  OneNowPersistsThroughAllTime → EarlierAndLaterEventsBecomeSimultaneous

/-- Aristotle's assessment of inherited accounts in *Physics* IV.10, 218a30-218b1: after
the existence puzzles, the nature of time remains obscure both from received views and from
the preceding inquiry.

Source: Aristotle, *Physics* IV.10, 218a30-218b1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NatureOfTimeRemainsObscureReading (NatureOfTimeIsClear : Prop) : Prop :=
  ¬ NatureOfTimeIsClear

/-- First inherited identification in Aristotle, *Physics* IV.10, 218b1-5: some identify
time with the motion of the whole, but a part of a revolution is a time while not itself a
complete revolution.

Source: Aristotle, *Physics* IV.10, 218b1-5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PartOfCosmicRevolutionIsTimeNotRevolutionReading
    (PartOfCosmicRevolutionIsTime PartIsCompleteRevolution : Prop) : Prop :=
  PartOfCosmicRevolutionIsTime ∧ ¬ PartIsCompleteRevolution

/-- Many-heavens objection in Aristotle, *Physics* IV.10, 218b5-8: if time were any
heaven's motion, multiple heavens would yield multiple simultaneous times.

Source: Aristotle, *Physics* IV.10, 218b5-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MultipleHeavensWouldYieldMultipleTimesReading
    (MultipleHeavensExist TimeIsMotionOfAnyHeaven
      MultipleSimultaneousTimesExist : Prop) : Prop :=
  MultipleHeavensExist ∧ TimeIsMotionOfAnyHeaven →
    MultipleSimultaneousTimesExist

/-- Second inherited identification in Aristotle, *Physics* IV.10, 218b8-13: some call the
sphere of the whole time because everything is both in time and in that sphere; Aristotle
rejects this resemblance as an inadequate account.

Source: Aristotle, *Physics* IV.10, 218b8-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CosmicSphereAccountOfTimeInadequateReading
    (EverythingIsInTime EverythingIsInCosmicSphere
      SharedContainmentEstablishesIdentity : Prop) : Prop :=
  EverythingIsInTime ∧ EverythingIsInCosmicSphere ∧
    ¬ SharedContainmentEstablishesIdentity

/-- Scope difference in Aristotle, *Physics* IV.10, 218b13-17: each motion or change is
only in its changing subject or wherever that subject happens to be, whereas time is alike
everywhere and with everything.

Source: Aristotle, *Physics* IV.10, 218b13-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionLocalWhileTimeUniversalReading
    (EachMotionIsLocalToChangingSubject TimeIsEverywhereAlike : Prop) : Prop :=
  EachMotionIsLocalToChangingSubject ∧ TimeIsEverywhereAlike

/-- Inferential bridge from scope in Aristotle, *Physics* IV.10, 218b13-17: if each motion
is local to its changing subject while time is everywhere alike, time is not motion.

Source: Aristotle, *Physics* IV.10, 218b13-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionTimeScopeDifferenceEntailsNonidentityReading
    (EachMotionIsLocalToChangingSubject TimeIsEverywhereAlike
      TimeIsMotion : Prop) : Prop :=
  (EachMotionIsLocalToChangingSubject ∧ TimeIsEverywhereAlike) →
    ¬ TimeIsMotion

/-- Speed asymmetry in Aristotle, *Physics* IV.10, 218b17-20: motion can be faster or
slower and is measured as such by time, while time is not faster or slower and is not
determined by time.

Source: Aristotle, *Physics* IV.10, 218b17-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionSpeedMeasuredByTimeNotConverselyReading
    (MotionCanBeFasterOrSlower TimeCanBeFasterOrSlower
      MotionSpeedMeasuredByTime TimeMeasuredByTime : Prop) : Prop :=
  MotionCanBeFasterOrSlower ∧ ¬ TimeCanBeFasterOrSlower ∧
    MotionSpeedMeasuredByTime ∧ ¬ TimeMeasuredByTime

/-- Aristotle's conclusion in *Physics* IV.10, 218b20: time is not motion or change.

Source: Aristotle, *Physics* IV.10, 218b20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeIsNotMotionReading (TimeIsMotion : Prop) : Prop :=
  ¬ TimeIsMotion

end TruthCore.Greek.Aristotle.Physics
