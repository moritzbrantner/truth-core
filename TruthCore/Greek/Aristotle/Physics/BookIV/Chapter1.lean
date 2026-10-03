import TruthCore.Greek.Aristotle.Physics.BookIII.Chapter8

namespace TruthCore.Greek.Aristotle.Physics

/--
Opening agenda in Aristotle, *Physics* IV.1, 208a27-208b1: the physicist must determine
whether place exists, how it exists, and what it is. The inquiry matters because existing
things are commonly supposed to be somewhere and locomotion is the most general and primary
kind of motion, yet inherited accounts do not settle place's nature.

Source: Aristotle, *Physics* IV.1, 208a27-208b1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PhysicalInquiryIntoPlaceRequiredReading
    (PhysicistMustDetermineWhetherPlaceExists
      PhysicistMustDetermineHowPlaceExists
      PhysicistMustDetermineWhatPlaceIs
      ExistingThingsCommonlySupposedSomewhere
      LocomotionIsPrimaryGeneralMotion
      InheritedAccountsDoNotSettlePlace : Prop) : Prop :=
  PhysicistMustDetermineWhetherPlaceExists ∧
    PhysicistMustDetermineHowPlaceExists ∧
      PhysicistMustDetermineWhatPlaceIs ∧
        ExistingThingsCommonlySupposedSomewhere ∧
          LocomotionIsPrimaryGeneralMotion ∧
            InheritedAccountsDoNotSettlePlace

/--
Premise from mutual replacement in Aristotle, *Physics* IV.1, 208b1-8: water leaves a
vessel-like region and air or another body later occupies the same region, while the bodies
enter and depart.

Source: Aristotle, *Physics* IV.1, 208b1-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BodiesMutuallyReplaceInSameRegionReading
    (WaterAndAirOccupySameRegionAtDifferentTimes
      BodiesEnterAndLeaveRegion : Prop) : Prop :=
  WaterAndAirOccupySameRegionAtDifferentTimes ∧ BodiesEnterAndLeaveRegion

/--
Inferential bridge in Aristotle, *Physics* IV.1, 208b1-8: if different bodies occupy the same
region at different times while entering and departing, the place or region is distinct from
both occupants.

Source: Aristotle, *Physics* IV.1, 208b1-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MutualReplacementImpliesDistinctPlaceReading
    (WaterAndAirOccupySameRegionAtDifferentTimes BodiesEnterAndLeaveRegion
      PlaceDistinctFromOccupyingBodies : Prop) : Prop :=
  WaterAndAirOccupySameRegionAtDifferentTimes ∧ BodiesEnterAndLeaveRegion →
    PlaceDistinctFromOccupyingBodies

/--
Conclusion of Aristotle's mutual-replacement consideration in *Physics* IV.1, 208b1-8:
place is something distinct from the bodies that successively occupy it.

Source: Aristotle, *Physics* IV.1, 208b1-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PlaceDistinctFromOccupyingBodiesReading
    (PlaceDistinctFromOccupyingBodies : Prop) : Prop :=
  PlaceDistinctFromOccupyingBodies

/--
Natural-motion consideration in Aristotle, *Physics* IV.1, 208b8-17: unimpeded simple
bodies move toward their own places—light bodies upward and heavy earthy bodies downward—so
place appears not only to exist but to possess a distinctive power.

Source: Aristotle, *Physics* IV.1, 208b8-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalMotionSuggestsPlaceHasPowerReading
    (SimpleBodiesMoveTowardOwnPlacesWhenUnimpeded
      LightBodiesMoveUpward
      HeavyEarthyBodiesMoveDownward
      PlaceAppearsToHavePower : Prop) : Prop :=
  SimpleBodiesMoveTowardOwnPlacesWhenUnimpeded ∧
    LightBodiesMoveUpward ∧
      HeavyEarthyBodiesMoveDownward ∧
        PlaceAppearsToHavePower

/--
Directional distinction in Aristotle, *Physics* IV.1, 208b17-25: right, left, up, and down
relative to us vary with our orientation, while natural up and down are distinguished by the
motions of light and heavy bodies. Mathematical objects have only the positional, relative
directions, not those directions by nature.

Source: Aristotle, *Physics* IV.1, 208b17-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalDirectionsDifferFromRelativeDirectionsReading
    (RelativeDirectionsVaryWithOrientation
      NaturalUpDownFixedByNaturalMotions
      MathematicalObjectsHaveOnlyPositionalDirections : Prop) : Prop :=
  RelativeDirectionsVaryWithOrientation ∧
    NaturalUpDownFixedByNaturalMotions ∧
      MathematicalObjectsHaveOnlyPositionalDirections

/--
Void-based consideration in Aristotle, *Physics* IV.1, 208b25-29: those who affirm void also
affirm place, because void would be place deprived of body. Together with the preceding
considerations, this supports supposing place distinct from bodies and sensible bodies in place.

Source: Aristotle, *Physics* IV.1, 208b25-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VoidTheoryPresupposesPlaceReading
    (VoidAffirmed VoidIsPlaceDeprivedOfBody
      PlaceDistinctFromBodies SupposedEverySensibleBodyInPlace : Prop) : Prop :=
  VoidAffirmed →
    VoidIsPlaceDeprivedOfBody ∧
      PlaceDistinctFromBodies ∧
        SupposedEverySensibleBodyInPlace

/--
Hesiodic priority consideration in Aristotle, *Physics* IV.1, 208b29-209a1: Hesiod's chaos
first can be read as prior room for beings. If nothing else exists without place while place
survives the destruction of its occupants, place would be prior to them.

This remains a dialectical consideration, not Aristotle's final ontology of place.

Source: Aristotle, *Physics* IV.1, 208b29-209a1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def HesiodicPlacePriorityConsiderationReading
    (HesiodicChaosReadAsPriorRoom
      OtherThingsCannotExistWithoutPlace
      PlaceCanExistWithoutCurrentOccupants
      PlaceWouldBePriorToOccupants : Prop) : Prop :=
  HesiodicChaosReadAsPriorRoom ∧
    OtherThingsCannotExistWithoutPlace ∧
      PlaceCanExistWithoutCurrentOccupants →
        PlaceWouldBePriorToOccupants

/--
Opening genus puzzle in Aristotle, *Physics* IV.1, 209a2-7: even granting that place exists,
one must determine whether it is a bodily bulk or another kind of nature before its genus is
known.

Source: Aristotle, *Physics* IV.1, 209a2-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PlaceGenusRemainsUndeterminedReading
    (PlaceExists
      PlaceMayBeBodilyBulk
      PlaceMayBeOtherNature
      PlaceGenusRequiresDetermination : Prop) : Prop :=
  PlaceExists ∧
    (PlaceMayBeBodilyBulk ∨ PlaceMayBeOtherNature) ∧
      PlaceGenusRequiresDetermination

/--
First premise of the body puzzle in Aristotle, *Physics* IV.1, 209a2-7: place has length,
breadth, and depth, the three dimensions by which body is bounded.

Source: Aristotle, *Physics* IV.1, 209a2-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PlaceHasThreeDimensionsReading (PlaceHasThreeDimensions : Prop) : Prop :=
  PlaceHasThreeDimensions

/--
Inferential bridge in Aristotle's *Physics* IV.1, 209a2-7: if three-dimensional place were
itself a body, place and its occupant would be two bodies in the same location; that is
impossible, so place is not a body.

Source: Aristotle, *Physics* IV.1, 209a2-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BodilyPlaceWouldDuplicateBodiesReading
    (PlaceHasThreeDimensions PlaceIsNotBody : Prop) : Prop :=
  PlaceHasThreeDimensions → PlaceIsNotBody

/--
Conclusion of the body puzzle in Aristotle, *Physics* IV.1, 209a2-7: place cannot itself be
a body.

Source: Aristotle, *Physics* IV.1, 209a2-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PlaceIsNotBodyReading (PlaceIsNotBody : Prop) : Prop :=
  PlaceIsNotBody

/--
Boundary puzzle in Aristotle, *Physics* IV.1, 209a7-13: if bodies have places, surfaces and
other boundaries should as well; yet a point cannot be distinguished from the place of that
point, casting doubt on a place distinct from every boundary.

Source: Aristotle, *Physics* IV.1, 209a7-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SurfacePointPlacePuzzleReading
    (BodiesHavingPlaceImpliesBoundariesHavePlace
      PointDistinctFromPlaceOfPoint
      DistinctPlaceForEveryBoundaryDoubtful : Prop) : Prop :=
  BodiesHavingPlaceImpliesBoundariesHavePlace ∧
    ¬ PointDistinctFromPlaceOfPoint ∧
      DistinctPlaceForEveryBoundaryDoubtful

/--
Category puzzle in Aristotle, *Physics* IV.1, 209a13-18: place seems neither an element nor
composed of elements, corporeal or incorporeal. It has magnitude without being a body, while
sensible elements are bodies and intelligible elements do not produce magnitude.

Source: Aristotle, *Physics* IV.1, 209a13-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PlaceNeitherElementNorElementCompositeReading
    (PlaceIsElement
      PlaceComposedOfElements
      PlaceHasMagnitude
      PlaceIsBody
      SensibleElementsAreBodies
      IntelligibleElementsProduceMagnitude : Prop) : Prop :=
  ¬ PlaceIsElement ∧
    ¬ PlaceComposedOfElements ∧
      PlaceHasMagnitude ∧
        ¬ PlaceIsBody ∧
          SensibleElementsAreBodies ∧
            ¬ IntelligibleElementsProduceMagnitude

/--
Causal-role puzzle in Aristotle, *Physics* IV.1, 209a18-23: place appears to be none of the
four causes of beings—not their matter, form, end, or source of motion.

Source: Aristotle, *Physics* IV.1, 209a18-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PlaceHasNoApparentFourCauseRoleReading
    (PlaceIsMaterialCause PlaceIsFormalCause PlaceIsFinalCause
      PlaceIsSourceOfMotionCause : Prop) : Prop :=
  ¬ PlaceIsMaterialCause ∧
    ¬ PlaceIsFormalCause ∧
      ¬ PlaceIsFinalCause ∧
        ¬ PlaceIsSourceOfMotionCause

/--
Zeno's regress puzzle in Aristotle, *Physics* IV.1, 209a23-26: if every existent is in a
place and place itself exists, place must be in another place, continuing without limit.

Source: Aristotle, *Physics* IV.1, 209a23-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ZenoPlaceRegressPuzzleReading
    (EveryExistentIsInPlace PlaceExists
      PlaceRequiresFurtherPlace InfinitePlaceRegress : Prop) : Prop :=
  EveryExistentIsInPlace ∧ PlaceExists →
    PlaceRequiresFurtherPlace ∧ InfinitePlaceRegress

/--
Growth puzzle and chapter conclusion in Aristotle, *Physics* IV.1, 209a26-30: if every body
is in place, every place contains a body, and each body's place is neither smaller nor larger,
then a growing body's place must grow with it. Such puzzles force inquiry into both what place
is and whether it exists.

Source: Aristotle, *Physics* IV.1, 209a26-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GrowingBodyPlacePuzzleReading
    (EveryBodyInPlace
      EveryPlaceContainsBody
      PlaceMatchesBodyMagnitude
      GrowingBodyRequiresGrowingPlace
      PlaceNatureAndExistenceRequireInquiry : Prop) : Prop :=
  EveryBodyInPlace ∧
    EveryPlaceContainsBody ∧
      PlaceMatchesBodyMagnitude →
        GrowingBodyRequiresGrowingPlace ∧
          PlaceNatureAndExistenceRequireInquiry

end TruthCore.Greek.Aristotle.Physics
