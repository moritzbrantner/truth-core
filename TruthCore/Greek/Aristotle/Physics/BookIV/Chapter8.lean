import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter7

namespace TruthCore.Greek.Aristotle.Physics

/-- Natural-direction objection in Aristotle, *Physics* IV.8, 214b12-18: simple bodies have
distinct natural locomotions—fire upward and earth downward toward the middle—so void cannot
be the cause of locomotion.

Source: Aristotle, *Physics* IV.8, 214b12-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalDirectionsShowVoidNotLocomotionCauseReading
    (SimpleBodiesHaveDistinctNaturalDirections
      VoidIsCauseOfLocomotion : Prop) : Prop :=
  SimpleBodiesHaveDistinctNaturalDirections → ¬ VoidIsCauseOfLocomotion

/-- Direction and rest puzzle in Aristotle, *Physics* IV.8, 214b18-24: if void is bodyless
place, there is no account of where an inserted body will move or how it will remain, since
it cannot move into the whole undifferentiated void.

Source: Aristotle, *Physics* IV.8, 214b18-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SeparatedVoidCannotDirectOrRestBodyReading
    (VoidIsBodylessPlace InsertedBodyHasDeterminateDirectionInVoid
      InsertedBodyHasGroundForRestInVoid : Prop) : Prop :=
  VoidIsBodylessPlace →
    ¬ InsertedBodyHasDeterminateDirectionInVoid ∧
      ¬ InsertedBodyHasGroundForRestInVoid

/-- Whole-part objection in Aristotle, *Physics* IV.8, 214b24-29: putting a body as a whole
in a separate permanent place does not put its unseparated parts in places rather than in the
whole; if no separate place exists, no such void exists either.

Source: Aristotle, *Physics* IV.8, 214b24-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def WholePartObjectionToSeparatedVoidReading
    (WholeInSeparatePermanentPlace UnseparatedPartsInSeparatePlaces
      SeparatePlaceExists SeparatedVoidExists : Prop) : Prop :=
  (WholeInSeparatePermanentPlace → ¬ UnseparatedPartsInSeparatePlaces) ∧
    (¬ SeparatePlaceExists → ¬ SeparatedVoidExists)

/-- Indifference-to-direction objection in Aristotle, *Physics* IV.8, 214b29-35: because
void as void admits no difference, nothing has a reason to move more or less toward one
region, so the very void alleged necessary for motion would instead require rest.

Source: Aristotle, *Physics* IV.8, 214b29-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def UndifferentiatedVoidWouldRequireRestReading
    (VoidAdmitsNoDirectionalDifference
      BodyHasReasonToMoveTowardOneVoidRegion
      BodyMustRestInVoid : Prop) : Prop :=
  VoidAdmitsNoDirectionalDifference →
    ¬ BodyHasReasonToMoveTowardOneVoidRegion ∧ BodyMustRestInVoid

/-- Directional facts in Aristotle, *Physics* IV.8, 215a6-13: infinite void has no up, down,
or middle, and void as privation has no directional differentiation.

Source: Aristotle, *Physics* IV.8, 215a6-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VoidHasNoDirectionalDifferentiationReading
    (InfiniteVoidHasUpDownOrMiddle VoidHasDirectionalDifferentiation : Prop) : Prop :=
  ¬ InfiniteVoidHasUpDownOrMiddle ∧ ¬ VoidHasDirectionalDifferentiation

/-- Bridge from directional indifference in Aristotle, *Physics* IV.8, 215a6-13: because
natural locomotion is differentiated, a void with no up, down, middle, or directional
difference cannot host natural motion.

Source: Aristotle, *Physics* IV.8, 215a1-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VoidLacksNaturalMotionReading
    (InfiniteVoidHasUpDownOrMiddle VoidHasDirectionalDifferentiation
      NaturalMotionInVoid : Prop) : Prop :=
  (¬ InfiniteVoidHasUpDownOrMiddle ∧ ¬ VoidHasDirectionalDifferentiation) →
    ¬ NaturalMotionInVoid

/-- Dependence of non-natural motion in Aristotle, *Physics* IV.8, 215a1-6: all motion is
natural or compulsory, and compulsory motion contrary to nature is posterior to natural
motion; if natural motion is absent, no motion remains.

Source: Aristotle, *Physics* IV.8, 215a1-6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoNaturalMotionEntailsNoMotionReading
    (NaturalMotionInVoid AnyMotionInVoid : Prop) : Prop :=
  ¬ NaturalMotionInVoid → ¬ AnyMotionInVoid

/-- Conclusion of Aristotle's directional reductio in *Physics* IV.8, 214b29-215a13: no
motion is possible in a separated, undifferentiated void.

Source: Aristotle, *Physics* IV.8, 214b29-215a13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoMotionInSeparatedVoidReading (AnyMotionInVoid : Prop) : Prop :=
  ¬ AnyMotionInVoid

/-- Projectile objection in Aristotle, *Physics* IV.8, 215a13-19: thrown bodies continue
after loss of contact through mutual replacement or a pushed medium; neither mechanism exists
in void, leaving no account of continued projectile motion there.

Source: Aristotle, *Physics* IV.8, 215a13-19 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ProjectileContinuationMechanismsAbsentInVoidReading
    (ProjectilesContinueAfterContact MutualReplacementContinuesProjectile
      PushedMediumContinuesProjectile ContinuationMechanismExistsInVoid : Prop) : Prop :=
  ProjectilesContinueAfterContact ∧
    (MutualReplacementContinuesProjectile ∨ PushedMediumContinuesProjectile) ∧
      ¬ ContinuationMechanismExistsInVoid

/-- No-stopping-point reductio in Aristotle, *Physics* IV.8, 215a19-22: void supplies no
reason for a moving body to stop here rather than there, so absent a stronger impediment it
must either remain at rest or continue without limit.

Source: Aristotle, *Physics* IV.8, 215a19-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VoidProvidesNoStoppingPointReading
    (VoidProvidesDeterminateStoppingReason StrongerImpedimentIntervenes
      BodyRemainsAtRest BodyMovesWithoutLimit : Prop) : Prop :=
  ¬ VoidProvidesDeterminateStoppingReason ∧ ¬ StrongerImpedimentIntervenes →
    BodyRemainsAtRest ∨ BodyMovesWithoutLimit

/-- Equal-yield objection in Aristotle, *Physics* IV.8, 215a22-24: if motion toward void is
explained by its yielding, void yields alike everywhere and a body should move in every
direction.

Source: Aristotle, *Physics* IV.8, 215a22-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VoidEqualYieldImpliesAllDirectionsReading
    (VoidYieldsEquallyEverywhere BodyWouldMoveInEveryDirection : Prop) : Prop :=
  VoidYieldsEquallyEverywhere → BodyWouldMoveInEveryDirection

/-- The two observed sources of speed differences in Aristotle, *Physics* IV.8, 215a24-29:
the same body moves at different speeds through different media, and otherwise comparable
bodies differ in speed with their weight or lightness.

Source: Aristotle, *Physics* IV.8, 215a24-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MediumAndMovingBodyDetermineSpeedReading
    (SameBodySpeedDiffersByMedium
      ComparableBodySpeedDiffersByWeightOrLightness : Prop) : Prop :=
  SameBodySpeedDiffersByMedium ∧
    ComparableBodySpeedDiffersByWeightOrLightness

/-- Medium-resistance account in Aristotle, *Physics* IV.8, 215a29-215b11: a medium impedes
motion, denser and less easily divided media impede more, and traversal times vary with that
resistance. This records Aristotle's proportional comparison without importing a modern law.

Source: Aristotle, *Physics* IV.8, 215a29-215b11 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MediumResistanceDeterminesTraversalTimeReading
    (MediumImpedesMotion DenserMediumImpedesMore
      EasierDivisionAllowsFasterTraversal
      TraversalTimesVaryWithMediumResistance : Prop) : Prop :=
  MediumImpedesMotion ∧ DenserMediumImpedesMore ∧
    EasierDivisionAllowsFasterTraversal ∧
      TraversalTimesVaryWithMediumResistance

/-- Ratio mismatch in Aristotle, *Physics* IV.8, 215b11-22: body bears no determinate ratio
of excess to void, as a number bears none to zero, so void and full admit no corresponding
ratio of media or motions.

Source: Aristotle, *Physics* IV.8, 215b11-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VoidAndFullHaveNoMotionRatioReading
    (VoidAndFullHaveMediumRatio MotionsThroughVoidAndFullHaveRatio : Prop) : Prop :=
  ¬ VoidAndFullHaveMediumRatio ∧ ¬ MotionsThroughVoidAndFullHaveRatio

/-- Finite-time supposition in Aristotle's reductio, *Physics* IV.8, 215b22-216a7: if a
body traversed a stretch of void in some finite time, a suitably rare full medium would be
traversed over the same distance in that same time.

Source: Aristotle, *Physics* IV.8, 215b22-216a7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FiniteVoidTraversalEntailsEqualFullVoidTraversalTimeReading
    (FiniteVoidTraversal EqualFullAndVoidTraversalTime : Prop) : Prop :=
  FiniteVoidTraversal → EqualFullAndVoidTraversalTime

/-- The impossible consequence in Aristotle's reductio, *Physics* IV.8, 216a1-7: the same
body cannot traverse equal distances through a full medium and void in equal time.

Source: Aristotle, *Physics* IV.8, 216a1-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EqualFullVoidTraversalTimeImpossibleReading
    (EqualFullAndVoidTraversalTime : Prop) : Prop :=
  ¬ EqualFullAndVoidTraversalTime

/-- Conclusion of Aristotle's finite-time reductio in *Physics* IV.8, 215b22-216a11: no
body traverses a stretch of void in a finite time.

Source: Aristotle, *Physics* IV.8, 215b22-216a11 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FiniteVoidTraversalImpossibleReading (FiniteVoidTraversal : Prop) : Prop :=
  ¬ FiniteVoidTraversal

/-- Summary of the ratio reductio in Aristotle, *Physics* IV.8, 216a8-12: any two finite
motions, through their finite times, bear a ratio to one another, whereas void and full do
not bear a ratio.

Source: Aristotle, *Physics* IV.8, 216a8-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FiniteMotionsButNotVoidAndFullHaveRatioReading
    (AnyTwoFiniteMotionsHaveRatio VoidAndFullHaveRatio : Prop) : Prop :=
  AnyTwoFiniteMotionsHaveRatio ∧ ¬ VoidAndFullHaveRatio

/-- Moving-body comparison in Aristotle, *Physics* IV.8, 216a12-20: otherwise comparable
bodies with greater weight or lightness traverse an equal full region faster because their
shape or impulse divides the medium more forcefully.

Source: Aristotle, *Physics* IV.8, 216a12-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GreaterImpulseDividesFullMediumFasterReading
    (GreaterWeightOrLightnessGivesGreaterImpulse
      GreaterImpulseDividesFullMediumFaster : Prop) : Prop :=
  GreaterWeightOrLightnessGivesGreaterImpulse →
    GreaterImpulseDividesFullMediumFaster

/-- Equal-speed reductio in Aristotle, *Physics* IV.8, 216a16-21: void supplies no medium
for greater shape or impulse to divide, so the void hypothesis makes all otherwise comparable
bodies move equally fast; Aristotle rejects that consequence as impossible.

Source: Aristotle, *Physics* IV.8, 216a16-21 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VoidSpeedEqualityReductioReading
    (SeparatedVoidExists AllComparableBodiesMoveEquallyFastInVoid : Prop) : Prop :=
  (SeparatedVoidExists → AllComparableBodiesMoveEquallyFastInVoid) ∧
    ¬ AllComparableBodiesMoveEquallyFastInVoid

/-- Separate-place consequence in Aristotle, *Physics* IV.8, 216a21-26: positing void as
separated in itself amounts to positing place as an independently separated interval, which
the preceding account of place has already rejected.

Source: Aristotle, *Physics* IV.8, 216a21-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SeparatedVoidWouldBeImpossibleSeparatePlaceReading
    (SeparatedVoidExists IndependentSeparatePlaceExists : Prop) : Prop :=
  (SeparatedVoidExists → IndependentSeparatePlaceExists) ∧
    ¬ IndependentSeparatePlaceExists

/-- Equal-volume displacement in Aristotle, *Physics* IV.8, 216a26-34: a cube inserted
into water displaces its own volume of water, and does the same in air even though this is
less evident to perception.

Source: Aristotle, *Physics* IV.8, 216a26-34 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CubeDisplacesEqualVolumeInMediaReading
    (CubeDisplacesEqualWaterVolume CubeDisplacesEqualAirVolume : Prop) : Prop :=
  CubeDisplacesEqualWaterVolume ∧ CubeDisplacesEqualAirVolume

/-- Displacement puzzle for void in Aristotle, *Physics* IV.8, 216a30-216b2: whereas a
body medium can move aside when the cube is inserted, void is no body and cannot be
displaced, so the previously empty interval would have to pass through the cube.

Source: Aristotle, *Physics* IV.8, 216a30-216b2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VoidCannotDisplaceAroundCubeReading
    (CubeInsertedIntoVoid PriorVoidIntervalPenetratesCube : Prop) : Prop :=
  CubeInsertedIntoVoid → PriorVoidIntervalPenetratesCube

/-- Magnitude-quality distinction in Aristotle, *Physics* IV.8, 216b2-10: the wooden
cube's volume is distinct in being from its hot, cold, heavy, or light attributes, even
though that volume is not separately existent, and it equals the interval it occupies.

Source: Aristotle, *Physics* IV.8, 216b2-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CubeVolumeDistinctFromQualitiesReading
    (CubeHasVolumeEqualToOccupiedInterval
      CubeVolumeDiffersInBeingFromSensibleQualities : Prop) : Prop :=
  CubeHasVolumeEqualToOccupiedInterval ∧
    CubeVolumeDiffersInBeingFromSensibleQualities

/-- Coincidence consequence in Aristotle, *Physics* IV.8, 216b7-12: on the separated-void
hypothesis, the cube's body and a void or place interval equal to it would occupy the same
region.

Source: Aristotle, *Physics* IV.8, 216b7-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CubeAndEqualVoidWouldCoincideReading
    (SeparatedVoidExists CubeAndEqualVoidCoincide : Prop) : Prop :=
  SeparatedVoidExists → CubeAndEqualVoidCoincide

/-- Unlimited-coincidence reductio in Aristotle, *Physics* IV.8, 216b10-12: if a body's
magnitude and an equal void interval can coincide, there is no principled stopping point at
two such magnitudes rather than arbitrarily many.

Source: Aristotle, *Physics* IV.8, 216b10-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SeparatedVoidEntailsUnlimitedCoincidenceReading
    (SeparatedVoidExists ArbitrarilyManyEqualMagnitudesCoincide : Prop) : Prop :=
  SeparatedVoidExists → ArbitrarilyManyEqualMagnitudesCoincide

/-- Aristotle's rejection of the coincidence consequence in *Physics* IV.8, 216b10-12:
arbitrarily many equal magnitudes cannot all coincide in the same region.

Source: Aristotle, *Physics* IV.8, 216b10-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def UnlimitedEqualMagnitudeCoincidenceImpossibleReading
    (ArbitrarilyManyEqualMagnitudesCoincide : Prop) : Prop :=
  ¬ ArbitrarilyManyEqualMagnitudesCoincide

/-- Redundancy of an extra interval in Aristotle, *Physics* IV.8, 216b12-17: a body keeps
its own volume while moving, so an equal attribute-free interval added around that volume
contributes nothing to its emplacement.

Source: Aristotle, *Physics* IV.8, 216b12-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AdditionalIntervalBeyondBodyVolumeContributesNothingReading
    (MovingBodyRetainsItsVolume
      AdditionalEqualIntervalContributesToEmplacement : Prop) : Prop :=
  MovingBodyRetainsItsVolume ∧
    ¬ AdditionalEqualIntervalContributesToEmplacement

/-- Perceptibility check in Aristotle, *Physics* IV.8, 216b17-20: separated void should be
discernible in moving things, but none is found; air is a body despite seeming empty, just as
water might escape recognition by iron fish unable to discriminate it by touch.

Source: Aristotle, *Physics* IV.8, 216b17-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoPerceptibleSeparatedVoidInMovingBodiesReading
    (SeparatedVoidPerceptibleInMovingBodies
      SeparatedVoidFoundWithinCosmos AirIsBodyDespiteAppearingEmpty : Prop) : Prop :=
  (SeparatedVoidPerceptibleInMovingBodies → SeparatedVoidFoundWithinCosmos) ∧
    ¬ SeparatedVoidFoundWithinCosmos ∧ AirIsBodyDespiteAppearingEmpty

/-- Aristotle's conclusion in *Physics* IV.8, 216b20-21: separated void does not exist.
The reading remains restricted to the chapter's target, rather than merging every ancient
or modern use of “void.”

Source: Aristotle, *Physics* IV.8, 216b20-21 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SeparatedVoidDoesNotExistReading (SeparatedVoidExists : Prop) : Prop :=
  ¬ SeparatedVoidExists

end TruthCore.Greek.Aristotle.Physics
