import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter2

namespace TruthCore.Greek.Aristotle.Physics

/--
Eight senses of one thing being "in" another in Aristotle, *Physics* IV.3, 210a14-24:
part in whole, whole in parts, species in genus, genus in a species' definition, form in
matter, affairs in a primary mover, a thing in its end, and a contained thing in place.

Source: Aristotle, *Physics* IV.3, 210a14-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EightSensesOfBeingInReading
    (PartInWhole WholeInParts WholeIsNothingBeyondParts
      SpeciesInGenus GenusInSpeciesDefinition
      FormInMatter InPrimaryMover InEnd InPlace : Prop) : Prop :=
  PartInWhole ∧
    WholeInParts ∧
      WholeIsNothingBeyondParts ∧
        SpeciesInGenus ∧
          GenusInSpeciesDefinition ∧
            FormInMatter ∧
              InPrimaryMover ∧
                InEnd ∧
                  InPlace

/--
Priority among the senses of "in" in Aristotle, *Physics* IV.3, 210a23-24: the strictest
or most authoritative sense is containment as in a vessel and, generally, being in place.

Source: Aristotle, *Physics* IV.3, 210a23-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SpatialContainmentIsStrictestInSenseReading
    (BeingInVesselOrPlaceIsStrictestSense : Prop) : Prop :=
  BeingInVesselOrPlaceIsStrictestSense

/--
Qualified self-location in Aristotle, *Physics* IV.3, 210a25-210b5: when the container and
contained are distinct parts of one whole, that whole may derivatively be said to be in
itself. Thus neither jar nor wine is separately in itself, while the wine-filled jar may be
so described through its parts; this is not primary self-location.

Source: Aristotle, *Physics* IV.3, 210a25-210b5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def QualifiedSelfLocationThroughPartsReading
    (ContainerAndContainedArePartsOfOneWhole
      WholeMayBeSaidInItselfThroughParts
      JarSeparatelyInItself
      WineSeparatelyInItself
      DerivativeSelfLocationIsPrimary : Prop) : Prop :=
  ContainerAndContainedArePartsOfOneWhole →
    WholeMayBeSaidInItselfThroughParts ∧
      ¬ JarSeparatelyInItself ∧
        ¬ WineSeparatelyInItself ∧
          ¬ DerivativeSelfLocationIsPrimary

/--
Role distinction in Aristotle, *Physics* IV.3, 210b5-17: the containing subject and what it
contains differ in account, nature, and capacity even if each is in the other in some respect.

Source: Aristotle, *Physics* IV.3, 210b5-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContainerAndContainedDifferInAccountReading
    (ContainerAndContainedDifferInAccount
      SurfaceAndWhiteDifferInNature
      SurfaceAndWhiteDifferInCapacity : Prop) : Prop :=
  ContainerAndContainedDifferInAccount ∧
    SurfaceAndWhiteDifferInNature ∧
      SurfaceAndWhiteDifferInCapacity

/--
Inferential bridge in Aristotle, *Physics* IV.3, 210b7-17: primary self-location would
require each of the two roles to be both container and contained, but those roles differ in
account; their distinction therefore excludes primary self-location.

Source: Aristotle, *Physics* IV.3, 210b7-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DistinctRolesExcludePrimarySelfLocationReading
    (ContainerAndContainedDifferInAccount PrimarySelfLocation : Prop) : Prop :=
  ContainerAndContainedDifferInAccount → ¬ PrimarySelfLocation

/--
Conclusion of Aristotle's role argument in *Physics* IV.3, 210b7-17: nothing can primarily
be in itself. This does not deny the derivative whole-through-parts usage distinguished
earlier in the chapter.

Source: Aristotle, *Physics* IV.3, 210b7-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PrimarySelfLocationImpossibleReading (PrimarySelfLocation : Prop) : Prop :=
  ¬ PrimarySelfLocation

/--
Incidental self-location objection in Aristotle, *Physics* IV.3, 210b17-22: if a receptive
container were incidentally in itself, both that container and what it receives would be in
the same thing, duplicating the occupants assigned to it.

Source: Aristotle, *Physics* IV.3, 210b17-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IncidentalSelfLocationDuplicatesOccupantsReading
    (IncidentalSelfLocation
      ContainerAndReceivedContentWouldBothBeInContainer : Prop) : Prop :=
  IncidentalSelfLocation → ContainerAndReceivedContentWouldBothBeInContainer

/--
Resolution of Zeno's place regress in Aristotle, *Physics* IV.3, 210b22-27: a first place
may be "in" something in a non-spatial sense, as health is in the hot as a state or heat in
a body as an affection. It need not therefore be in another place, and no infinite regress
follows.

Source: Aristotle, *Physics* IV.3, 210b22-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NonSpatialInSenseBlocksZenoRegressReading
    (FirstPlaceMayBeInAnotherNonSpatially
      FirstPlaceMustBeInAnotherPlace
      InfinitePlaceRegressRequired : Prop) : Prop :=
  FirstPlaceMayBeInAnotherNonSpatially →
    ¬ FirstPlaceMustBeInAnotherPlace ∧ ¬ InfinitePlaceRegressRequired

/--
Container-content distinction in Aristotle, *Physics* IV.3, 210b27-31: a vessel is no part
of its content, and in the primary containing relation the container differs from what it
contains.

Source: Aristotle, *Physics* IV.3, 210b27-31 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PrimaryContainerDistinctFromContainedReading
    (VesselIsPartOfContent PrimaryContainerDistinctFromContained : Prop) : Prop :=
  ¬ VesselIsPartOfContent ∧ PrimaryContainerDistinctFromContained

end TruthCore.Greek.Aristotle.Physics
