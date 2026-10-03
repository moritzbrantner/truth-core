import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter2

namespace TruthCore.Greek.Aristotle.Physics

/-- A primary now exists in every time as the common boundary of past and future in
Aristotle, *Physics* VI.3, 233b33-234a5.

Source: Aristotle, *Physics* VI.3, 233b33-234a5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PrimaryNowCommonPastFutureBoundaryReading
    (PrimaryNowExistsInEveryTime
      PrimaryNowCommonBoundaryOfPastFuture : Prop) : Prop :=
  PrimaryNowExistsInEveryTime ∧ PrimaryNowCommonBoundaryOfPastFuture

/-- If the terminal now of the past and the initial now of the future were distinct,
continuous time would lie between them and be divisible in Aristotle, *Physics* VI.3,
234a5-12.

Source: Aristotle, *Physics* VI.3, 234a5-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DistinctPastFutureNowsRequireDivisibleIntervalReading
    (PastFutureNowsDistinct InterveningDivisibleTime : Prop) : Prop :=
  PastFutureNowsDistinct → InterveningDivisibleTime

/-- A divisible now would put part of the past in the future and part of the future
in the past, and would cease to be a primary now in its own right, in Aristotle,
*Physics* VI.3, 234a10-19.

Source: Aristotle, *Physics* VI.3, 234a10-19 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DivisibleNowMixesPastFutureReading
    (NowDivisible PastInFuture FutureInPast NowPrimaryInItself : Prop) : Prop :=
  NowDivisible → (PastInFuture ∧ FutureInPast ∧ ¬ NowPrimaryInItself)

/-- The terminal now of the past and the initial now of the future are the same now
in Aristotle, *Physics* VI.3, 234a5-22.

Source: Aristotle, *Physics* VI.3, 234a5-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PastFutureShareSameNowReading
    (PastFutureShareSameNow : Prop) : Prop :=
  PastFutureShareSameNow

/-- Aristotle's inferential transition in *Physics* VI.3, 234a20-24: if past and
future share the same primary now, that now is indivisible, since division would
reproduce the rejected consequences.

Source: Aristotle, *Physics* VI.3, 234a20-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SamePrimaryNowImpliesIndivisibleReading
    (PastFutureShareSameNow PrimaryNowIndivisible : Prop) : Prop :=
  PastFutureShareSameNow → PrimaryNowIndivisible

/-- The primary now is indivisible in Aristotle, *Physics* VI.3, 233b33-234a24.

Source: Aristotle, *Physics* VI.3, 233b33-234a24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PrimaryNowIndivisibleReading
    (PrimaryNowIndivisible : Prop) : Prop :=
  PrimaryNowIndivisible

/-- The primary now is not divisible in Aristotle, *Physics* VI.3, 234a20-30.

Source: Aristotle, *Physics* VI.3, 234a20-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PrimaryNowNotDivisibleReading
    (PrimaryNowDivisible : Prop) : Prop :=
  ¬ PrimaryNowDivisible

/-- If anything moved in the now, comparing faster and slower movers would produce
a motion in less than the whole now and thereby divide it, in Aristotle,
*Physics* VI.3, 234a24-30.

Source: Aristotle, *Physics* VI.3, 234a24-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionInNowImpliesNowDivisibleReading
    (MotionInNow PrimaryNowDivisible : Prop) : Prop :=
  MotionInNow → PrimaryNowDivisible

/-- Nothing moves in the now in Aristotle, *Physics* VI.3, 234a24-31.

Source: Aristotle, *Physics* VI.3, 234a24-31 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NothingMovesInNowReading
    (MotionInNow : Prop) : Prop :=
  ¬ MotionInNow

/-- Rest belongs to what is naturally capable of moving, but is not moving when,
where, and how it is naturally capable, in Aristotle, *Physics* VI.3, 234a31-34.

Source: Aristotle, *Physics* VI.3, 234a31-34 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RestRequiresMotionCapacityReading
    (RestInNow MotionPossibleInNow : Prop) : Prop :=
  RestInNow → MotionPossibleInNow

/-- Nothing is naturally capable of motion in the now in Aristotle, *Physics* VI.3,
234a30-34.

Source: Aristotle, *Physics* VI.3, 234a30-34 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NothingCapableOfMotionInNowReading
    (MotionPossibleInNow : Prop) : Prop :=
  ¬ MotionPossibleInNow

/-- Nothing rests in the now in Aristotle, *Physics* VI.3, 234a31-234b8.

Source: Aristotle, *Physics* VI.3, 234a31-234b8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NothingRestsInNowReading
    (RestInNow : Prop) : Prop :=
  ¬ RestInNow

/-- If motion throughout one time and rest throughout another belonged at their
shared boundary now, motion and rest would coincide there, in Aristotle,
*Physics* VI.3, 234a34-234b4.

Source: Aristotle, *Physics* VI.3, 234a34-234b4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SharedBoundaryWouldCoincideMotionRestReading
    (MotionAndRestWouldCoincideAtSharedNow : Prop) : Prop :=
  MotionAndRestWouldCoincideAtSharedNow

/-- Rest requires the same condition now and before, but there is no before within
the now, in Aristotle, *Physics* VI.3, 234b4-8.

Source: Aristotle, *Physics* VI.3, 234b4-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RestRequiresBeforeAbsentFromNowReading
    (RestRequiresSameConditionNowAndBefore BeforeExistsWithinNow : Prop) : Prop :=
  RestRequiresSameConditionNowAndBefore ∧ ¬ BeforeExistsWithinNow

/-- What moves must move in time, and what rests must rest in time, in Aristotle,
*Physics* VI.3, 234b8-9.

Source: Aristotle, *Physics* VI.3, 234b8-9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionAndRestRequireTimeReading
    (MotionRequiresTime RestRequiresTime : Prop) : Prop :=
  MotionRequiresTime ∧ RestRequiresTime

end TruthCore.Greek.Aristotle.Physics
