import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter3

namespace TruthCore.Greek.Aristotle.Physics

/-- Essential constraints on place in Aristotle, *Physics* IV.4, 210b32-211a6. Place contains
what it places without being a part of it; the immediate place is equal to the thing, can be
left behind and separated, has up and down, and is where natural bodies move and rest.

Source: Aristotle, *Physics* IV.4, 210b32-211a6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PlaceEssentialConstraintsReading
    (PlaceContainsLocatedThing PlaceIsPartOfLocatedThing
      ImmediatePlaceEqualToLocatedThing PlaceSeparableFromLocatedThing
      PlaceHasUpAndDown NaturalBodiesMoveAndRestInOwnPlaces : Prop) : Prop :=
  PlaceContainsLocatedThing ∧ ¬ PlaceIsPartOfLocatedThing ∧
    ImmediatePlaceEqualToLocatedThing ∧ PlaceSeparableFromLocatedThing ∧
      PlaceHasUpAndDown ∧ NaturalBodiesMoveAndRestInOwnPlaces

/-- Methodological demand in Aristotle, *Physics* IV.4, 211a6-11: an adequate account must
state what place is, solve the puzzles, preserve its accepted attributes, and explain why the
subject generated its characteristic difficulties.

Source: Aristotle, *Physics* IV.4, 211a6-11 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AdequatePlaceAccountCriteriaReading
    (AccountStatesWhatPlaceIs AccountSolvesPlacePuzzles
      AccountPreservesAcceptedPlaceAttributes AccountExplainsPlaceDifficulties : Prop) : Prop :=
  AccountStatesWhatPlaceIs ∧ AccountSolvesPlacePuzzles ∧
    AccountPreservesAcceptedPlaceAttributes ∧ AccountExplainsPlaceDifficulties

/-- Motive for the place inquiry in Aristotle, *Physics* IV.4, 211a11-16: without local
motion place would not have been investigated; the heaven is especially thought to be in
place because it is always in motion.

Source: Aristotle, *Physics* IV.4, 211a11-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def LocalMotionMotivatesPlaceInquiryReading
    (LocalMotionExists PlaceInquiryArises HeavenAlwaysMoves
      HeavenEspeciallyThoughtInPlace : Prop) : Prop :=
  (LocalMotionExists → PlaceInquiryArises) ∧
    HeavenAlwaysMoves ∧ HeavenEspeciallyThoughtInPlace

/-- Kinds of spatially relevant change in Aristotle, *Physics* IV.4, 211a16-24. Locomotion
and growth or diminution alter where a thing is; some movers move in actuality through
themselves, while parts and attributes may change place incidentally with their subjects.

Source: Aristotle, *Physics* IV.4, 211a16-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SpatialChangeKindsReading
    (LocomotionChangesPlace GrowthAndDiminutionChangePlace
      SomeThingsMovePerSe SomeThingsMoveIncidentally
      AttributesMoveOnlyWithTheirSubjects : Prop) : Prop :=
  LocomotionChangesPlace ∧ GrowthAndDiminutionChangePlace ∧
    SomeThingsMovePerSe ∧ SomeThingsMoveIncidentally ∧
      AttributesMoveOnlyWithTheirSubjects

/-- Immediate-place restriction in Aristotle, *Physics* IV.4, 211a23-29: something is in the
heaven through the air, but not in all the air. Its proper place is the air's immediately
containing boundary, which is equal rather than larger than the located thing.

Source: Aristotle, *Physics* IV.4, 211a23-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ImmediatePlaceIsEqualContainingBoundaryReading
    (LocatedInHeavenThroughAir LocatedInAllAir
      ImmediateContainingBoundaryIsPlace ImmediatePlaceEqualToLocatedThing : Prop) : Prop :=
  LocatedInHeavenThroughAir ∧ ¬ LocatedInAllAir ∧
    ImmediateContainingBoundaryIsPlace ∧ ImmediatePlaceEqualToLocatedThing

/-- Continuous versus separated containment in Aristotle, *Physics* IV.4, 211a29-211b5. An
undivided continuous item is in its container as a part in a whole; when divided and touching,
it is spatially in the container's immediate boundary, which is no part of it and is equal.

Source: Aristotle, *Physics* IV.4, 211a29-211b5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContinuousPartAndSeparatedPlaceReading
    (UndividedContinuousIsPartInWhole SeparatedTouchingIsInPlace
      ImmediateBoundaryIsPartOfContained ImmediateBoundaryEqualToContained : Prop) : Prop :=
  UndividedContinuousIsPartInWhole ∧ SeparatedTouchingIsInPlace ∧
    ¬ ImmediateBoundaryIsPartOfContained ∧ ImmediateBoundaryEqualToContained

/-- Motion contrast in Aristotle, *Physics* IV.4, 211a35-211b10: what is continuous with a
whole moves with it, whereas a separated body moves within its container whether that
container moves or not, as a hand moves with the body but water moves in a vessel.

Source: Aristotle, *Physics* IV.4, 211a35-211b10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MovingWithWholeVersusWithinContainerReading
    (ContinuousPartMovesWithWhole SeparatedBodyMovesWithinContainer
      ContainerMayMoveOrRemain HandMovesWithBody WaterMovesInVessel : Prop) : Prop :=
  ContinuousPartMovesWithWhole ∧ SeparatedBodyMovesWithinContainer ∧
    ContainerMayMoveOrRemain ∧ HandMovesWithBody ∧ WaterMovesInVessel

/-- The four exhaustive candidates in Aristotle, *Physics* IV.4, 211b5-10: place must be
form, matter, an independent interval between the container's boundaries, or the containing
boundary itself where no such further interval exists.

Source: Aristotle, *Physics* IV.4, 211b5-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FourPlaceCandidatesReading
    (PlaceIsForm PlaceIsMatter PlaceIsIndependentInterval
      PlaceIsContainingBoundaryAtContact : Prop) : Prop :=
  PlaceIsForm ∨ PlaceIsMatter ∨ PlaceIsIndependentInterval ∨
    PlaceIsContainingBoundaryAtContact

/-- Form-place boundary distinction in Aristotle, *Physics* IV.4, 211b10-15: form seems to
be place because both are coincident boundaries, but form bounds the contained thing while
place belongs to the containing body.

Source: Aristotle, *Physics* IV.4, 211b10-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FormAndPlaceBoundDifferentBodiesReading
    (FormBoundsContainedThing PlaceBoundsContainingBody
      CoincidentBoundariesHaveSameSubject : Prop) : Prop :=
  FormBoundsContainedThing ∧ PlaceBoundsContainingBody ∧
    ¬ CoincidentBoundariesHaveSameSubject

/-- Rejection of an independent interval in Aristotle, *Physics* IV.4, 211b15-29. Bodily
replacement makes such an interval seem to persist, but some body always occupies the region;
if a permanent independent interval existed, infinitely many changing and coincident places,
including places of places, would result.

Source: Aristotle, *Physics* IV.4, 211b15-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IndependentIntervalPlaceRejectedReading
    (ReplacementSuggestsPersistentInterval SomeBodyAlwaysOccupiesRegion
      IndependentIntervalExists InfiniteCoincidentPlacesWouldResult
      PlacesOfPlacesWouldResult : Prop) : Prop :=
  ReplacementSuggestsPersistentInterval ∧ SomeBodyAlwaysOccupiesRegion ∧
    (IndependentIntervalExists →
      InfiniteCoincidentPlacesWouldResult ∧ PlacesOfPlacesWouldResult) ∧
        ¬ IndependentIntervalExists

/-- Matter-place comparison in Aristotle, *Physics* IV.4, 211b29-212a2. Successive bodies
in one region can resemble one substrate through qualitative change, making matter appear
to be place; but matter neither separates from nor contains the thing, while place does both.

Source: Aristotle, *Physics* IV.4, 211b29-212a2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MatterPlaceAppearanceAndRejectionReading
    (SuccessionSuggestsMatterPlaceAnalogy MatterSeparableFromThing
      MatterContainsThing PlaceSeparableFromThing PlaceContainsThing : Prop) : Prop :=
  SuccessionSuggestsMatterPlaceAnalogy ∧ ¬ MatterSeparableFromThing ∧
    ¬ MatterContainsThing ∧ PlaceSeparableFromThing ∧ PlaceContainsThing

/-- Result of Aristotle's three eliminations in *Physics* IV.4, 211b10-212a5: place is
neither the contained thing's form, nor its matter, nor a permanent independent interval.

Source: Aristotle, *Physics* IV.4, 211b10-212a5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FormMatterIntervalExcludedReading
    (PlaceIsForm PlaceIsMatter PlaceIsIndependentInterval : Prop) : Prop :=
  ¬ PlaceIsForm ∧ ¬ PlaceIsMatter ∧ ¬ PlaceIsIndependentInterval

/-- Conclusion of the four-candidate elimination in Aristotle, *Physics* IV.4, 212a2-7:
place is the boundary of the containing body at which it contacts the contained body capable
of locomotion.

Source: Aristotle, *Physics* IV.4, 212a2-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PlaceIsContainingBoundaryAtContactReading
    (PlaceIsContainingBoundaryAtContact : Prop) : Prop :=
  PlaceIsContainingBoundaryAtContact

/-- Sources of the difficulty about place in Aristotle, *Physics* IV.4, 212a7-15: matter and
form appear along with it, replacement occurs in a stationary container, and air's apparent
incorporeality makes the vessel's interior look like an empty independent interval.

Source: Aristotle, *Physics* IV.4, 212a7-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PlaceDifficultySourcesReading
    (MatterAndFormAppearWithPlace StationaryContainerHostsReplacement
      AirAppearsIncorporeal VesselInteriorAppearsEmptyInterval : Prop) : Prop :=
  MatterAndFormAppearWithPlace ∧ StationaryContainerHostsReplacement ∧
    AirAppearsIncorporeal ∧ VesselInteriorAppearsEmptyInterval

/-- Immobility refinement in Aristotle, *Physics* IV.4, 212a14-21: a vessel is movable
place, while place is an immovable vessel. A moving river segment containing a boat therefore
acts more as vessel than place; the whole stable river illustrates why place is the first
immobile boundary of what contains.

Source: Aristotle, *Physics* IV.4, 212a14-21 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PlaceIsFirstImmobileContainingBoundaryReading
    (VesselIsMovablePlace PlaceIsImmovableVessel
      MovingRiverSegmentActsAsVessel WholeRiverActsAsPlace
      PlaceIsFirstImmobileContainingBoundary : Prop) : Prop :=
  VesselIsMovablePlace ∧ PlaceIsImmovableVessel ∧
    MovingRiverSegmentActsAsVessel ∧ WholeRiverActsAsPlace ∧
      PlaceIsFirstImmobileContainingBoundary

/-- Directional and coincidence consequences in Aristotle, *Physics* IV.4, 212a21-30: the
stable cosmic middle and outer extreme ground natural down and up; place appears surface-like
and container-like, and is coincident with its bounded occupant because their boundaries meet.

Source: Aristotle, *Physics* IV.4, 212a21-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalDirectionsAndBoundaryCoincidenceReading
    (CosmicMiddleGroundsDown CosmicExtremeGroundsUp
      PlaceAppearsSurfaceAndContainer PlaceCoincidentWithLocatedThing : Prop) : Prop :=
  CosmicMiddleGroundsDown ∧ CosmicExtremeGroundsUp ∧
    PlaceAppearsSurfaceAndContainer ∧ PlaceCoincidentWithLocatedThing

end TruthCore.Greek.Aristotle.Physics
