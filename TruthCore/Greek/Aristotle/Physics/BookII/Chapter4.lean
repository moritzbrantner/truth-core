import TruthCore.Greek.Aristotle.Physics.BookII.Chapter3

namespace TruthCore.Greek.Aristotle.Physics

/--
Opening inquiry in Aristotle, *Physics* II.4, 195b31-36: chance and spontaneity are counted
among causes, so inquiry must determine how they fit the established causes, whether they are
the same or different, and what each is.

The questions remain questions here; the chapter does not yet provide Aristotle's account.

Source: Aristotle, *Physics* II.4, 195b31-36 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChanceSpontaneityRequireCausalInquiryReading
    (ChanceSpontaneityCountedAmongCauses
      TheirPlaceAmongCausesRequiresInquiry
      TheirIdentityOrDifferenceRequiresInquiry
      TheirNaturesRequireInquiry : Prop) : Prop :=
  ChanceSpontaneityCountedAmongCauses ∧
    TheirPlaceAmongCausesRequiresInquiry ∧
      TheirIdentityOrDifferenceRequiresInquiry ∧
        TheirNaturesRequireInquiry

/--
Attributed denial in Aristotle, *Physics* II.4, 195b36-196a11: some deny that anything
happens by chance because every alleged case has a definite cause; the earlier investigators'
silence about chance is taken to support that denial.

The marketplace example's shopping intention is preserved as the opponents' definite cause,
not accepted here as Aristotle's full explanation of the unexpected meeting.

Source: Aristotle, *Physics* II.4, 195b36-196a11 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AttributedDenialOfChanceReading
    (NothingHappensByChance
      EveryAllegedChanceEventHasDefiniteCause
      AncientSilenceSupportsDenial : Prop) : Prop :=
  NothingHappensByChance ∧
    EveryAllegedChanceEventHasDefiniteCause ∧
      AncientSilenceSupportsDenial

/--
Aristotle's dialectical reply in *Physics* II.4, 196a11-17: even while acknowledging that
each event can be referred to some cause, ordinary judgments distinguish events that are by
chance from those that are not; earlier thinkers therefore should at least have discussed
chance.

Source: Aristotle, *Physics* II.4, 196a11-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DefiniteCauseCompatibleWithChanceDistinctionReading
    (EachEventReferableToSomeCause
      SomeEventsJudgedByChance
      SomeEventsJudgedNotByChance
      EarlierThinkersShouldDiscussChance : Prop) : Prop :=
  EachEventReferableToSomeCause ∧
    SomeEventsJudgedByChance ∧
      SomeEventsJudgedNotByChance ∧
        EarlierThinkersShouldDiscussChance

/--
Historical criticism in Aristotle, *Physics* II.4, 196a17-24: early physicists did not place
chance among such causes as Love, Strife, Mind, or fire, yet sometimes employed chance in
their explanations.

Source: Aristotle, *Physics* II.4, 196a17-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EarlyPhysicistsOmitYetUseChanceReading
    (EarlyPhysicistsRecognizeChanceAsBasicCause
      EarlyPhysicistsSometimesUseChance : Prop) : Prop :=
  ¬ EarlyPhysicistsRecognizeChanceAsBasicCause ∧
    EarlyPhysicistsSometimesUseChance

/--
Attributed Empedoclean examples in Aristotle, *Physics* II.4, 196a19-24: Empedocles says
air separates in whichever way it chances and that most animal parts came to be by chance.

This records Aristotle's report, not an endorsement or a complete reconstruction of
Empedocles' cosmology or zoogony.

Source: Aristotle, *Physics* II.4, 196a19-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AttributedEmpedocleanChanceExamplesReading
    (AirSeparationOccursAsItChances
      MostAnimalPartsComeToBeByChance : Prop) : Prop :=
  AirSeparationOccursAsItChances ∧
    MostAnimalPartsComeToBeByChance

/--
First attributed premise in Aristotle's *Physics* II.4, 196a24-196b1 criticism: animals and
plants neither exist nor come to be by chance, but from nature, mind, or another such cause,
as the regular outcomes from different seeds indicate.

Source: Aristotle, *Physics* II.4, 196a24-196b1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AttributedOrganismsNotFromChanceReading
    (OrganismsComeToBeByChance
      OrganismsHaveNatureMindOrSimilarCause
      SeedKindsYieldRegularOutcomes : Prop) : Prop :=
  ¬ OrganismsComeToBeByChance ∧
    OrganismsHaveNatureMindOrSimilarCause ∧
      SeedKindsYieldRegularOutcomes

/--
Second attributed premise in Aristotle's *Physics* II.4, 196a24-196b1 criticism: some make
the vortex and separating motion arise spontaneously and thereby arrange the heavens and all
worlds, without a cause like that assigned to organisms.

Source: Aristotle, *Physics* II.4, 196a24-196b1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AttributedCosmosFromSpontaneityReading
    (CosmosArisesFromSpontaneity
      CosmosHasOrganismLikeCause : Prop) : Prop :=
  CosmosArisesFromSpontaneity ∧ ¬ CosmosHasOrganismLikeCause

/--
Inferential bridge in Aristotle's *Physics* II.4, 196a24-196b1 criticism: denying chance for
regular organisms while assigning the heavens to spontaneity creates a causal asymmetry that
requires explanation.

Source: Aristotle, *Physics* II.4, 196a24-196b1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def OrganismCosmosAsymmetryRequiresExplanationReading
    (OrganismsComeToBeByChance CosmosArisesFromSpontaneity
      CausalAsymmetryRequiresExplanation : Prop) : Prop :=
  ¬ OrganismsComeToBeByChance ∧ CosmosArisesFromSpontaneity →
    CausalAsymmetryRequiresExplanation

/--
Conclusion of Aristotle's *Physics* II.4, 196a24-196b1 criticism: the reported denial of
chance for organisms together with spontaneous cosmogenesis produces a causal asymmetry that
deserves explicit examination.

Source: Aristotle, *Physics* II.4, 196a24-196b1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PredecessorOrganismCosmosAsymmetryReading
    (CausalAsymmetryRequiresExplanation : Prop) : Prop :=
  CausalAsymmetryRequiresExplanation

/--
Observational criticism in Aristotle, *Physics* II.4, 196b1-5: it is especially strange to
assign the heavens to spontaneity when nothing spontaneous is observed there, while many
chance events occur among the terrestrial things the predecessors deny are from chance.

Source: Aristotle, *Physics* II.4, 196b1-5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ObservedChanceDistributionReversesPredecessorAssignmentReading
    (SpontaneousEventsObservedInHeavens
      ChanceEventsObservedAmongTerrestrialThings : Prop) : Prop :=
  ¬ SpontaneousEventsObservedInHeavens ∧
    ChanceEventsObservedAmongTerrestrialThings

/--
Alternative attributed view in Aristotle, *Physics* II.4, 196b5-7: some regard chance as a
cause but as inscrutable to human thought because it is divine or especially daimonic.

No endorsement of the theological description is implied.

Source: Aristotle, *Physics* II.4, 196b5-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AttributedDivineInscrutableChanceReading
    (ChanceIsCause
      ChanceInscrutableToHumanThought
      ChanceIsDivineOrDaimonic : Prop) : Prop :=
  ChanceIsCause ∧
    ChanceInscrutableToHumanThought ∧
      ChanceIsDivineOrDaimonic

end TruthCore.Greek.Aristotle.Physics
