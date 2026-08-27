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

end TruthCore.Greek.Aristotle.Physics
