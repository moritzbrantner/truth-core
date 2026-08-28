import TruthCore.Greek.Aristotle.Physics.BookV.Chapter2

namespace TruthCore.Greek.Aristotle.Physics

/-- Together, apart, and contact in Aristotle, *Physics* V.3, 226b22-24: things are
together when they occupy one primary place, apart when they occupy different places,
and in contact when their extremities are together.

Source: Aristotle, *Physics* V.3, 226b22-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TogetherApartAndContactDefinitionsReading
    (TogetherInOnePrimaryPlace ApartInDifferentPlaces
      ContactWhenExtremitiesTogether : Prop) : Prop :=
  TogetherInOnePrimaryPlace ∧ ApartInDifferentPlaces ∧
    ContactWhenExtremitiesTogether

/-- What is between belongs among contraries and requires at least three terms in
Aristotle, *Physics* V.3, 226b25-31 and 227a7-9: it is what a naturally and continuously
changing thing reaches before the contrary at which its change ends.

Source: Aristotle, *Physics* V.3, 226b25-31 and 227a7-9 (Bekker pagination; Ross
transposes 227a7-9 before 226b26-27).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BetweenAmongContrariesRequiresThreeReading
    (BetweenBelongsAmongContraries BetweenRequiresAtLeastThreeTerms
      ChangingThingNaturallyReachesBetweenBeforeContraryEnd : Prop) : Prop :=
  BetweenBelongsAmongContraries ∧ BetweenRequiresAtLeastThreeTerms ∧
    ChangingThingNaturallyReachesBetweenBeforeContraryEnd

/-- Continuous motion leaves no gap, or only the smallest possible gap, in the thing
through which motion occurs rather than in time, in Aristotle, *Physics* V.3,
226b28-33. The characterization applies to local and other changes.

Source: Aristotle, *Physics* V.3, 226b28-33 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContinuousMotionNoMaterialGapReading
    (NoOrSmallestGapInThingMovedThrough GapInTimeDefinesDiscontinuity
      AppliesToLocalAndOtherChanges : Prop) : Prop :=
  NoOrSmallestGapInThingMovedThrough ∧ ¬ GapInTimeDefinesDiscontinuity ∧
    AppliesToLocalAndOtherChanges

/-- Local contraries are the termini most distant along a straight line in Aristotle,
*Physics* V.3, 226b33-34; the shortest line is determinate, and what is determinate
serves as a measure.

Source: Aristotle, *Physics* V.3, 226b33-34 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def LocalContrariesMaximallyDistantOnStraightLineReading
    (LocalContrariesMaximallyDistantOnStraightLine
      ShortestLineDeterminate DeterminateServesAsMeasure : Prop) : Prop :=
  LocalContrariesMaximallyDistantOnStraightLine ∧ ShortestLineDeterminate ∧
    DeterminateServesAsMeasure

/-- Succession in Aristotle, *Physics* V.3, 226b34-227a9: a successor is later in a
determinate order of position, form, or another respect, with nothing of the same kind
between it and that which it succeeds. Something of another kind may intervene.

Source: Aristotle, *Physics* V.3, 226b34-227a9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SuccessionNothingOfSameKindBetweenReading
    (SuccessorLaterInDeterminateOrder NothingSameKindBetween
      SomethingDifferentKindMayBeBetween : Prop) : Prop :=
  SuccessorLaterInDeterminateOrder ∧ NothingSameKindBetween ∧
    SomethingDifferentKindMayBeBetween

/-- Contiguity in Aristotle, *Physics* V.3, 227a10: things are contiguous when they
are in succession and touch.

Source: Aristotle, *Physics* V.3, 227a10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContiguousIsSuccessiveAndTouchingReading
    (InSuccession Touching : Prop) : Prop :=
  InSuccession ∧ Touching

/-- Continuity is a species of contiguity in Aristotle, *Physics* V.3, 227a10-16:
the touching limits become one and the same, so continuous things naturally form a
unity through their contact.

Source: Aristotle, *Physics* V.3, 227a10-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContinuousWhenTouchingLimitsBecomeOneReading
    (IsContiguous TouchingLimitsBecomeOne NaturallyFormsUnityByContact : Prop) : Prop :=
  IsContiguous ∧ TouchingLimitsBecomeOne ∧ NaturallyFormsUnityByContact

end TruthCore.Greek.Aristotle.Physics
