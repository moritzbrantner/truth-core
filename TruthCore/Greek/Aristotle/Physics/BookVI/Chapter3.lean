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

end TruthCore.Greek.Aristotle.Physics
