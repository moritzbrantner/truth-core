import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter8

namespace TruthCore.Greek.Aristotle.Physics

/-- In Zeno's arrow argument, the flying arrow is at rest in every now because at
each now it occupies a space equal to itself, as presented by Aristotle in
*Physics* VI.9, 239b5-7.

Source: Aristotle, *Physics* VI.9, 239b5-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ZenoArrowAtRestInEveryNowReading
    (ArrowAtRestInEveryNow : Prop) : Prop :=
  ArrowAtRestInEveryNow

/-- Zeno's argument infers that an arrow resting in every now is stationary in
Aristotle's presentation in *Physics* VI.9, 239b5-8.

Source: Aristotle, *Physics* VI.9, 239b5-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RestInEveryNowEntailsStationaryArrowReading
    (ArrowAtRestInEveryNow ArrowIsStationary : Prop) : Prop :=
  ArrowAtRestInEveryNow → ArrowIsStationary

/-- Zeno's attributed conclusion is that the flying arrow is stationary in
Aristotle, *Physics* VI.9, 239b5-8; Aristotle immediately rejects the temporal
composition premise of this argument.

Source: Aristotle, *Physics* VI.9, 239b5-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ZenoArrowStationaryConclusionReading
    (ArrowIsStationary : Prop) : Prop :=
  ArrowIsStationary

/-- Time is not composed of indivisible nows, just as no magnitude is composed of
indivisible items, so Zeno's arrow argument rests on a false assumption in
Aristotle, *Physics* VI.9, 239b8-9.

Source: Aristotle, *Physics* VI.9, 239b8-9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeAndMagnitudeNotComposedOfIndivisiblesReading
    (TimeComposedOfIndivisibleNows MagnitudeComposedOfIndivisibles : Prop) : Prop :=
  ¬ TimeComposedOfIndivisibleNows ∧ ¬ MagnitudeComposedOfIndivisibles

/-- Aristotle enumerates four Zeno arguments about motion: the dichotomy, Achilles,
the arrow, and the moving rows in the stadium, in *Physics* VI.9, 239b9-10.

Source: Aristotle, *Physics* VI.9, 239b9-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ZenoFourMotionArgumentsReading
    (DichotomyArgument AchillesArgument ArrowArgument StadiumArgument : Prop) : Prop :=
  DichotomyArgument ∧ AchillesArgument ∧ ArrowArgument ∧ StadiumArgument

/-- Zeno's dichotomy argument says motion cannot reach its endpoint because the
moving thing must first reach the halfway point, in Aristotle, *Physics* VI.9,
239b10-14.

Source: Aristotle, *Physics* VI.9, 239b10-14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ZenoDichotomyHalfBeforeEndpointReading
    (MustReachHalfBeforeEndpoint EndpointCannotBeReached : Prop) : Prop :=
  MustReachHalfBeforeEndpoint → EndpointCannotBeReached

/-- Zeno's Achilles argument says the fastest runner never catches the slower,
because the pursuer must first reach each place from which the pursued has already
advanced, in Aristotle, *Physics* VI.9, 239b14-20.

Source: Aristotle, *Physics* VI.9, 239b14-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ZenoAchillesLeavesSlowerAlwaysAheadReading
    (PursuerMustReachEachPriorPlace SlowerAlwaysRemainsAhead : Prop) : Prop :=
  PursuerMustReachEachPriorPlace → SlowerAlwaysRemainsAhead

/-- Achilles has the same underlying divisional error and the same solution as the
dichotomy, differing only because its successive added magnitudes are not obtained
by bisection, in Aristotle, *Physics* VI.9, 239b18-27.

Source: Aristotle, *Physics* VI.9, 239b18-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AchillesSharesDichotomyErrorAndSolutionReading
    (SameUnderlyingDivisionalError SameSolution AddedMagnitudesNotBisected : Prop) : Prop :=
  SameUnderlyingDivisionalError ∧ SameSolution ∧ AddedMagnitudesNotBisected

/-- The pursued is not caught while it remains ahead, but it is nevertheless caught
if traversal of the finite distance is granted, so Zeno's assertion that what is
ahead is never caught is false, in Aristotle, *Physics* VI.9, 239b27-30.

Source: Aristotle, *Physics* VI.9, 239b27-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FiniteDistanceTraversalAllowsOvertakingReading
    (FiniteDistanceCanBeTraversed SlowerRunnerIsCaught : Prop) : Prop :=
  FiniteDistanceCanBeTraversed → SlowerRunnerIsCaught

/-- The arrow syllogism depends on treating time as composed of indivisible nows;
without that premise its conclusion does not follow, in Aristotle, *Physics* VI.9,
239b30-33.

Source: Aristotle, *Physics* VI.9, 239b30-33 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ArrowSyllogismDependsOnNowCompositionReading
    (TimeComposedOfIndivisibleNows ArrowSyllogismValid : Prop) : Prop :=
  ¬ TimeComposedOfIndivisibleNows → ¬ ArrowSyllogismValid

/-- Zeno's fourth argument sets equal rows moving at equal speed in opposite
directions past equal bodies in the stadium and alleges that half a time equals its
double, in Aristotle, *Physics* VI.9, 239b33-240a1.

Source: Aristotle, *Physics* VI.9, 239b33-240a1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ZenoStadiumSetupAndAllegedConclusionReading
    (EqualRowsMoveOppositeDirections EqualSpeeds HalfTimeEqualsDoubleTime : Prop) : Prop :=
  EqualRowsMoveOppositeDirections ∧ EqualSpeeds ∧ HalfTimeEqualsDoubleTime

/-- The stadium inference requires equal magnitudes traversed at equal speed to take
equal times whether the comparison is with a moving row or a stationary row, in
Aristotle's diagnosis in *Physics* VI.9, 240a1-5.

Source: Aristotle, *Physics* VI.9, 240a1-5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def StadiumInferenceDependsOnMovingStationaryEqualTimeReading
    (StadiumInferenceValid MovingAndStationaryComparisonsTakeEqualTime : Prop) : Prop :=
  StadiumInferenceValid → MovingAndStationaryComparisonsTakeEqualTime

/-- It is false that passing an equal moving magnitude and passing an equal
stationary magnitude at equal speed take equal times, so the stadium argument
conflates relative and stationary comparisons, in Aristotle, *Physics* VI.9,
240a1-5.

Source: Aristotle, *Physics* VI.9, 240a1-5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MovingStationaryEqualTimePremiseFalseReading
    (MovingAndStationaryComparisonsTakeEqualTime : Prop) : Prop :=
  ¬ MovingAndStationaryComparisonsTakeEqualTime

/-- In Zeno's stadium arrangement, a body in one moving row passes every body in the
oppositely moving row while a body in the other passes only half the stationary row,
so the two comparisons count different relative crossings, in Aristotle,
*Physics* VI.9, 240a5-15.

Source: Aristotle, *Physics* VI.9, 240a5-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def StadiumRelativeRowsCrossDifferentCountsReading
    (OppositeRowPassesAll MovingRowPassesHalfStationary : Prop) : Prop :=
  OppositeRowPassesAll ∧ MovingRowPassesHalfStationary

/-- Zeno's stadium inference is invalid because it depends on the false equal-time
premise for moving and stationary comparisons in Aristotle, *Physics* VI.9,
240a1-17.

Source: Aristotle, *Physics* VI.9, 240a1-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def StadiumInferenceInvalidReading
    (StadiumInferenceValid : Prop) : Prop :=
  ¬ StadiumInferenceValid

end TruthCore.Greek.Aristotle.Physics
