import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter4

namespace TruthCore.Greek.Aristotle.Physics

/-- External-container condition in Aristotle, *Physics* IV.5, 212a31-33: a body is in place
exactly when there is another body outside it that contains it.

Source: Aristotle, *Physics* IV.5, 212a31-33 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ExternalContainingBodyConditionReading
    (HasExternalContainingBody BodyIsInPlace : Prop) : Prop :=
  BodyIsInPlace ↔ HasExternalContainingBody

/-- Parts and whole in Aristotle, *Physics* IV.5, 212a33-212b4: even in a hypothetical body
of water without an outer container, parts move because they contain one another; the whole
does not simultaneously change place as a whole, though it may rotate, while up-down motion
belongs to bodies admitting condensation and rarefaction.

Source: Aristotle, *Physics* IV.5, 212a33-212b4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PartsAndWholeDifferInPlaceMotionReading
    (PartsMutuallyContainAndMove WholeSimultaneouslyChangesPlace
      WholeMayRotate CondensableRarefiableBodiesMoveUpDown : Prop) : Prop :=
  PartsMutuallyContainAndMove ∧ ¬ WholeSimultaneouslyChangesPlace ∧
    WholeMayRotate ∧ CondensableRarefiableBodiesMoveUpDown

/-- Potential and actual emplacement in Aristotle, *Physics* IV.5, 212b4-7: parts of a
continuous homogeneous body are potentially in place; once separated but touching like a
heap, they are actually in place.

Source: Aristotle, *Physics* IV.5, 212b4-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PotentialAndActualEmplacementOfPartsReading
    (ContinuousHomogeneousPartsPotentiallyInPlace
      SeparatedTouchingPartsActuallyInPlace : Prop) : Prop :=
  ContinuousHomogeneousPartsPotentiallyInPlace ∧
    SeparatedTouchingPartsActuallyInPlace

/-- Per-se and incidental emplacement in Aristotle, *Physics* IV.5, 212b7-14: bodies movable
by locomotion or growth are somewhere through themselves; soul and the heaven are in place
only incidentally or through parts, whose mutual containment permits circular motion.

Source: Aristotle, *Physics* IV.5, 212b7-14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PerSeAndIncidentalEmplacementReading
    (MovableBodiesPerSeInPlace SoulIncidentallyInPlace
      HeavenIncidentallyInPlaceThroughParts HeavenPartsMutuallyContain : Prop) : Prop :=
  MovableBodiesPerSeInPlace ∧ SoulIncidentallyInPlace ∧
    HeavenIncidentallyInPlaceThroughParts ∧ HeavenPartsMutuallyContain

/-- Cosmic exterior premise in Aristotle, *Physics* IV.5, 212b14-18: to be somewhere requires
a distinct containing thing, but nothing lies outside the whole heaven to contain it.

Source: Aristotle, *Physics* IV.5, 212b14-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NothingContainsWholeHeavenReading
    (NothingOutsideWholeHeaven ExternalBodyContainsWholeHeaven : Prop) : Prop :=
  NothingOutsideWholeHeaven ∧ ¬ ExternalBodyContainsWholeHeaven

/-- Conclusion in Aristotle, *Physics* IV.5, 212b7-18: the whole heaven is not anywhere and
is not in a place, because no external body contains it. This does not deny places to its parts.

Source: Aristotle, *Physics* IV.5, 212b7-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def WholeHeavenNotInPlaceReading (WholeHeavenIsInPlace : Prop) : Prop :=
  ¬ WholeHeavenIsInPlace

/-- Nested cosmic containment in Aristotle, *Physics* IV.5, 212b18-22: place is not the
heaven as a whole but its innermost stationary boundary touching the movable body; earth is
in water, water in air, air in aether, and aether in heaven, with no further container.

Source: Aristotle, *Physics* IV.5, 212b18-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NestedCosmicContainmentReading
    (PlaceIsHeavenAsWhole PlaceIsInnermostStationaryHeavenBoundary
      EarthInWater WaterInAir AirInAether AetherInHeaven
      HeavenInFurtherContainer : Prop) : Prop :=
  ¬ PlaceIsHeavenAsWhole ∧ PlaceIsInnermostStationaryHeavenBoundary ∧
    EarthInWater ∧ WaterInAir ∧ AirInAether ∧ AetherInHeaven ∧
      ¬ HeavenInFurtherContainer

/-- Resolution of earlier place puzzles in Aristotle, *Physics* IV.5, 212b22-29. On the
boundary account, place need not grow with its body, points need no places, two bodies do not
share one place, and place is no corporeal interval; place is "somewhere" only as a boundary
in what it bounds, and only movable body is in place.

Source: Aristotle, *Physics* IV.5, 212b22-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BoundaryAccountResolvesPlacePuzzlesReading
    (PlaceGrowsWithBody PointRequiresPlace TwoBodiesShareOnePlace
      PlaceIsCorporealInterval PlaceInPlaceSpatially
      PlaceInBoundedThingAsBoundary OnlyMovableBodyIsInPlace : Prop) : Prop :=
  ¬ PlaceGrowsWithBody ∧ ¬ PointRequiresPlace ∧ ¬ TwoBodiesShareOnePlace ∧
    ¬ PlaceIsCorporealInterval ∧ ¬ PlaceInPlaceSpatially ∧
      PlaceInBoundedThingAsBoundary ∧ OnlyMovableBodyIsInPlace

/-- Natural motion and rest in Aristotle, *Physics* IV.5, 212b29-213a1: unforced adjacent
and touching bodies are akin and interact, while naturally united bodies do not affect each
other; a body in its proper place relates as a separable part to a whole, explaining motion
toward and rest in its own place.

Source: Aristotle, *Physics* IV.5, 212b29-213a1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalMotionAndRestThroughAffinityReading
    (UnforcedAdjacentBodiesAreAkin TouchingBodiesInteract
      NaturallyUnitedBodiesDoNotInteract BodyInPlaceAsPartToWhole
      BodiesMoveToAndRestInOwnPlaces : Prop) : Prop :=
  UnforcedAdjacentBodiesAreAkin ∧ TouchingBodiesInteract ∧
    NaturallyUnitedBodiesDoNotInteract ∧ BodyInPlaceAsPartToWhole ∧
      BodiesMoveToAndRestInOwnPlaces

/-- Provisional water-air comparison and chapter close in Aristotle, *Physics* IV.5,
213a1-11: water and air stand as potentiality and actuality in different respects, touching
while distinct and becoming organically united when actually one. Aristotle marks this
account as provisional and closes the inquiry into whether place exists and what it is.

Source: Aristotle, *Physics* IV.5, 213a1-11 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def WaterAirPotentialityContactReading
    (WaterPotentiallyAir AirPotentiallyWaterInAnotherWay
      DistinctWaterAirTouch ActuallyOneWaterAirOrganicallyUnited
      AccountProvisional PlaceInquiryCompleted : Prop) : Prop :=
  WaterPotentiallyAir ∧ AirPotentiallyWaterInAnotherWay ∧
    DistinctWaterAirTouch ∧ ActuallyOneWaterAirOrganicallyUnited ∧
      AccountProvisional ∧ PlaceInquiryCompleted

end TruthCore.Greek.Aristotle.Physics
