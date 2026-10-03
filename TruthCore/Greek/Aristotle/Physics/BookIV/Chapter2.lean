import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter1

namespace TruthCore.Greek.Aristotle.Physics

/--
Common and proper place in Aristotle, *Physics* IV.2, 209a31-209b1: a common place contains
all the bodies within it, while a body's proper place is the first or immediate container
that contains no more than that body. Attribution to a more remote place may proceed through
nested containers.

Source: Aristotle, *Physics* IV.2, 209a31-209b1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CommonAndProperPlaceDistinctionReading
    (CommonPlaceContainsAllBodies
      ProperPlaceIsImmediateContainer
      ProperPlaceContainsNoMoreThanItsBody
      RemotePlacePredicationMayProceedThroughContainers : Prop) : Prop :=
  CommonPlaceContainsAllBodies ∧
    ProperPlaceIsImmediateContainer ∧
      ProperPlaceContainsNoMoreThanItsBody ∧
        RemotePlacePredicationMayProceedThroughContainers

/--
The initial form and matter candidates in Aristotle, *Physics* IV.2, 209b1-10. If proper
place is the body's first container, it looks like a boundary and hence like form; considered
instead as the interval of a magnitude, it looks like the indeterminate matter bounded by form.
These are candidate identifications, not Aristotle's final account.

Source: Aristotle, *Physics* IV.2, 209b1-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FormAndMatterPlaceCandidatesReading
    (ProperPlaceIsFirstContainer
      FirstContainerIsBoundary
      BoundarySuggestsFormCandidate
      PlaceRegardedAsMagnitudeInterval
      MagnitudeIntervalSuggestsMatterCandidate : Prop) : Prop :=
  (ProperPlaceIsFirstContainer →
      FirstContainerIsBoundary ∧ BoundarySuggestsFormCandidate) ∧
    (PlaceRegardedAsMagnitudeInterval → MagnitudeIntervalSuggestsMatterCandidate)

/--
Aristotle's report of Plato in *Physics* IV.2, 209b10-17: Plato identifies matter and
`chōra` in the *Timaeus* and, despite a different account of the participant in the unwritten
teachings, identifies place and `chōra`. Aristotle credits him alone among predecessors with
attempting to say what place is.

Source: Aristotle, *Physics* IV.2, 209b10-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PlatoMatterSpaceIdentificationReading
    (PlatoIdentifiesMatterAndChoraInTimaeus
      PlatoIdentifiesPlaceAndChora
      PlatoAloneAmongPredecessorsAttemptsAccountOfPlace : Prop) : Prop :=
  PlatoIdentifiesMatterAndChoraInTimaeus ∧
    PlatoIdentifiesPlaceAndChora ∧
      PlatoAloneAmongPredecessorsAttemptsAccountOfPlace

/--
Epistemic qualification in Aristotle, *Physics* IV.2, 209b17-21: if place were matter or
form, identifying it would demand especially close inquiry because matter and form are not
easily recognized apart; nevertheless, Aristotle says that excluding both is not difficult.

Source: Aristotle, *Physics* IV.2, 209b17-21 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MatterFormCandidatesRequireCloseInquiryReading
    (MatterAndFormNotEasilyKnownApart
      PlaceAsMatterOrFormWouldBeDifficultToKnow
      ExcludingMatterAndFormIsNotDifficult : Prop) : Prop :=
  MatterAndFormNotEasilyKnownApart ∧
    PlaceAsMatterOrFormWouldBeDifficultToKnow ∧
      ExcludingMatterAndFormIsNotDifficult

/--
Replacement and vessel consideration in Aristotle, *Physics* IV.2, 209b21-30: unlike a
thing's matter and form, its place can be separated from it as bodies replace one another.
A vessel is a movable place and no part of its occupant, so place is neither a part nor a
state of the occupant while containing it.

Source: Aristotle, *Physics* IV.2, 209b21-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PlaceSeparableContainerReading
    (BodiesReplaceOneAnother
      VesselIsMovablePlace
      PlaceSeparableFromOccupant
      PlaceContainsOccupant
      PlaceIsPartOfOccupant
      PlaceIsStateOfOccupant : Prop) : Prop :=
  BodiesReplaceOneAnother ∧
    VesselIsMovablePlace ∧
      PlaceSeparableFromOccupant ∧
        PlaceContainsOccupant ∧
          ¬ PlaceIsPartOfOccupant ∧
            ¬ PlaceIsStateOfOccupant

/--
Inferential bridge in Aristotle, *Physics* IV.2, 209b30-33: insofar as place is separable
from the located thing it is not that thing's form, and insofar as it contains the thing it
is other than the thing's matter.

Source: Aristotle, *Physics* IV.2, 209b30-33 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SeparabilityAndContainmentExcludeFormMatterReading
    (PlaceSeparableFromOccupant PlaceContainsOccupant
      PlaceIsForm PlaceIsMatter : Prop) : Prop :=
  PlaceSeparableFromOccupant ∧ PlaceContainsOccupant →
    ¬ PlaceIsForm ∧ ¬ PlaceIsMatter

/--
Conclusion of Aristotle's separability and containment test in *Physics* IV.2, 209b30-33:
place is neither the located thing's form nor its matter.

Source: Aristotle, *Physics* IV.2, 209b30-33 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PlaceNeitherFormNorMatterReading (PlaceIsForm PlaceIsMatter : Prop) : Prop :=
  ¬ PlaceIsForm ∧ ¬ PlaceIsMatter

/--
Natural-motion objection in Aristotle, *Physics* IV.2, 210a2-5: matter and form do not have
motion or the natural directional contrast of up and down, so neither can account for a
body's locomotion to its own place.

Source: Aristotle, *Physics* IV.2, 210a2-5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalMotionExcludesMatterFormPlaceReading
    (BodiesMoveToOwnPlaces
      MatterOrFormHasMotionAndNaturalDirections
      PlaceIsMatterOrForm : Prop) : Prop :=
  BodiesMoveToOwnPlaces ∧
    ¬ MatterOrFormHasMotionAndNaturalDirections →
      ¬ PlaceIsMatterOrForm

/--
Regress objection in Aristotle, *Physics* IV.2, 210a5-9: if place were a body's form or
matter, it would change and move with that body and therefore itself be in a place, so there
would be a place of place.

Source: Aristotle, *Physics* IV.2, 210a5-9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MatterFormPlaceProducesPlaceOfPlaceReading
    (PlaceIsMatterOrForm
      MatterAndFormMoveWithBody
      PlaceIsInPlace : Prop) : Prop :=
  PlaceIsMatterOrForm → MatterAndFormMoveWithBody ∧ PlaceIsInPlace

/--
Transformation puzzle and chapter close in Aristotle, *Physics* IV.2, 210a9-13: if place
were matter or form, the production of water from air would destroy the former place without
an intelligible account of that destruction. Aristotle closes by saying that he has stated
both why place must be something and the puzzles about its substance.

Source: Aristotle, *Physics* IV.2, 210a9-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TransformationChallengesMatterFormPlaceReading
    (PlaceIsMatterOrForm
      AirBecomesWater
      FormerPlaceWouldBeDestroyed
      DestructionOfPlaceRequiresExplanation
      ReasonsForPlaceAndPuzzlesAboutSubstanceStated : Prop) : Prop :=
  (PlaceIsMatterOrForm ∧ AirBecomesWater →
      FormerPlaceWouldBeDestroyed ∧ DestructionOfPlaceRequiresExplanation) ∧
    ReasonsForPlaceAndPuzzlesAboutSubstanceStated

end TruthCore.Greek.Aristotle.Physics
