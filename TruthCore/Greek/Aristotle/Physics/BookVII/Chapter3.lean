import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter2

namespace TruthCore.Greek.Aristotle.Physics

/-- Aristotle announces that everything altered is altered by sensible things and
that alteration belongs only to subjects said to be affected in themselves by
sensible things, in *Physics* VII.3, 245b3-5.

This records the chapter's scope thesis without identifying Aristotle's sensibles
with any modern category of physical stimulus.

Source: Aristotle, *Physics* VII.3, 245b3-5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AlterationRestrictedToSensibleAffectionReading
    (EveryAlteredThingAlteredBySensibles
      AlterationOnlyInPerSeSensiblyAffectedSubjects : Prop) : Prop :=
  EveryAlteredThingAlteredBySensibles ∧
    AlterationOnlyInPerSeSensiblyAffectedSubjects

/-- Shape and form, as well as bodily or psychic habits and their acquisition or
loss, are initially excluded from alteration in Aristotle, *Physics* VII.3,
245b5-8. The following parts of the chapter supply the distinct arguments for
these exclusions.

Source: Aristotle, *Physics* VII.3, 245b5-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ShapesFormsAndHabitsNotAlterationsReading
    (ShapesAndFormsNotAlterations
      HabitsAndTheirAcquisitionOrLossNotAlterations : Prop) : Prop :=
  ShapesAndFormsNotAlterations ∧
    HabitsAndTheirAcquisitionOrLossNotAlterations

/-- When a shaped or ordered product is completed, it is denominated from its
material rather than predicated straightforwardly as that material: the statue is
brazen, the pyramid waxen, and the bed wooden, in Aristotle, *Physics* VII.3,
245b8-12.

Source: Aristotle, *Physics* VII.3, 245b8-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ShapedProductDenominatedFromMatterReading
    (CompletedShapedProductDenominatedFromMatter : Prop) : Prop :=
  CompletedShapedProductDenominatedFromMatter

/-- By contrast with a shaped product, matter that has been affected and altered
is predicated by the affection: bronze or wax is called wet, hot, or hard, in
Aristotle, *Physics* VII.3, 245b12-16.

Source: Aristotle, *Physics* VII.3, 245b12-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AlteredMatterPredicatedByAffectionReading
    (AlteredMatterPredicatedByAffection : Prop) : Prop :=
  AlteredMatterPredicatedByAffection

/-- Aristotle takes the contrast between denomination in formation and
predication in affection to show that generations are not alterations in
*Physics* VII.3, 245b16-246a4.

The conditional records Aristotle's inferential transition; it does not claim
that this linguistic contrast is a generally sufficient modern criterion for
distinguishing kinds of change.

Source: Aristotle, *Physics* VII.3, 245b16-246a4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FormationPredicationContrastEntailsGenerationNotAlterationReading
    (CompletedShapedProductDenominatedFromMatter
      AlteredMatterPredicatedByAffection GenerationIsAlteration : Prop) : Prop :=
  (CompletedShapedProductDenominatedFromMatter ∧
      AlteredMatterPredicatedByAffection) →
    ¬ GenerationIsAlteration

/-- Generations are not alterations, in Aristotle, *Physics* VII.3,
245b16-246a4.

Source: Aristotle, *Physics* VII.3, 245b16-246a4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GenerationIsNotAlterationReading
    (GenerationIsAlteration : Prop) : Prop :=
  ¬ GenerationIsAlteration

/-- The generation of a thing may require something underlying, such as its
matter, to be altered by condensation, rarefaction, heating, or cooling; the
generated thing is nevertheless not thereby altered, and its generation is not
alteration, in Aristotle, *Physics* VII.3, 246a4-10.

The possibility wording preserves Aristotle's tentative `ἴσως` rather than
strengthening the passage into an unrestricted necessity claim.

Source: Aristotle, *Physics* VII.3, 246a4-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GenerationMayInvolveUnderlyingAlterationReading
    (GenerationMayRequireUnderlyingAlteration GeneratedThingItselfAltered
      GenerationIsAlteration : Prop) : Prop :=
  GenerationMayRequireUnderlyingAlteration ∧
    ¬ GeneratedThingItselfAltered ∧
    ¬ GenerationIsAlteration

/-- Habits are classified as virtues or vices; virtue is a perfection in which a
thing is most fully according to nature, while vice is the corruption of and
departure from that perfection, in Aristotle, *Physics* VII.3, 246a10-18.

Source: Aristotle, *Physics* VII.3, 246a10-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VirtueViceHabitsArePerfectionsOrDeparturesReading
    (HabitsClassifiedAsVirtuesOrVices VirtueIsPerfection
      ViceIsCorruptionAndDeparture : Prop) : Prop :=
  HabitsClassifiedAsVirtuesOrVices ∧
    VirtueIsPerfection ∧ ViceIsCorruptionAndDeparture

/-- Just as completing a house by adding its coping or tiling perfects rather
than alters the house, virtue and vice are respectively perfections and
departures rather than alterations, in Aristotle, *Physics* VII.3,
246a18-246b3.

Source: Aristotle, *Physics* VII.3, 246a18-246b3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def HouseCompletionAnalogyForHabitsReading
    (HouseCompletionIsPerfectionRatherThanAlteration
      VirtuesArePerfectionsAndVicesDepartures : Prop) : Prop :=
  HouseCompletionIsPerfectionRatherThanAlteration ∧
    VirtuesArePerfectionsAndVicesDepartures

/-- Neither virtue nor vice is an alteration, in Aristotle, *Physics* VII.3,
246a10-246b3.

Source: Aristotle, *Physics* VII.3, 246a10-246b3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VirtueAndViceAreNotAlterationsReading
    (VirtueIsAlteration ViceIsAlteration : Prop) : Prop :=
  ¬ VirtueIsAlteration ∧ ¬ ViceIsAlteration

/-- Bodily virtues such as health, good condition, beauty, and strength are
relational dispositions: mixtures or symmetries among internal hot and cold
factors or between them and the environment, disposing their subject well or
badly toward its characteristic affections, in Aristotle, *Physics* VII.3,
246b3-10.

Source: Aristotle, *Physics* VII.3, 246b3-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BodilyVirtuesAreRelationalDispositionsReading
    (BodilyVirtuesAndVicesAreRelationalDispositions : Prop) : Prop :=
  BodilyVirtuesAndVicesAreRelationalDispositions

/-- Relatives are not themselves alterations and, in Aristotle's classification,
do not intrinsically undergo alteration, generation, or any other change, in
*Physics* VII.3, 246b10-12.

This is kept as Aristotle's categorical premise rather than silently equated
with a modern theory of relational properties.

Source: Aristotle, *Physics* VII.3, 246b10-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RelativeStatesAdmitNoIntrinsicChangeReading
    (RelativeStatesAdmitNoIntrinsicChange : Prop) : Prop :=
  RelativeStatesAdmitNoIntrinsicChange

/-- From the classification of habits as virtues or vices, their relational
character, and the premise that relatives admit no intrinsic change, Aristotle
infers that neither habits nor their acquisition or loss are alterations in
*Physics* VII.3, 246b3-15.

Source: Aristotle, *Physics* VII.3, 246b3-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RelationalHabitAccountEntailsNoHabitAlterationReading
    (HabitsClassifiedAsVirtuesOrVices
      BodilyVirtuesAndVicesAreRelationalDispositions
      RelativeStatesAdmitNoIntrinsicChange
      HabitsOrTheirAcquisitionOrLossAreAlterations : Prop) : Prop :=
  (HabitsClassifiedAsVirtuesOrVices ∧
      BodilyVirtuesAndVicesAreRelationalDispositions ∧
      RelativeStatesAdmitNoIntrinsicChange) →
    ¬ HabitsOrTheirAcquisitionOrLossAreAlterations

/-- Neither habits nor their acquisition or loss are alterations, in Aristotle,
*Physics* VII.3, 246b10-15.

Source: Aristotle, *Physics* VII.3, 246b10-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def HabitsAndAcquisitionOrLossAreNotAlterationsReading
    (HabitsOrTheirAcquisitionOrLossAreAlterations : Prop) : Prop :=
  ¬ HabitsOrTheirAcquisitionOrLossAreAlterations

/-- Habits may arise and perish only while underlying subjects or qualities—hot
and cold, dry and wet, or their primary bearers—are altered; virtue and vice then
dispose their subject toward the relevant affections, in Aristotle, *Physics*
VII.3, 246b13-20.

The modal wording preserves Aristotle's qualified `ἴσως ... ἀνάγκη`.

Source: Aristotle, *Physics* VII.3, 246b13-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def HabitsMayAriseThroughUnderlyingAlterationReading
    (HabitsMayAriseOrPerishThroughUnderlyingAlteration
      VirtueAndViceDisposeSubjectTowardAffections : Prop) : Prop :=
  HabitsMayAriseOrPerishThroughUnderlyingAlteration ∧
    VirtueAndViceDisposeSubjectTowardAffections

/-- Psychic habits are likewise relational dispositions: their virtues are
perfections disposing the subject well toward its proper affections and their
vices are departures disposing it badly; neither they nor their acquisition or
loss are alterations, in Aristotle, *Physics* VII.3, 246b20-247a5.

Source: Aristotle, *Physics* VII.3, 246b20-247a5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PsychicHabitsAreRelationalNotAlterationsReading
    (PsychicHabitsAreRelational PsychicVirtuesArePerfections
      PsychicVicesAreDepartures PsychicVirtueDisposesWell
      PsychicViceDisposesBadly
      PsychicHabitsOrTheirAcquisitionOrLossAreAlterations : Prop) : Prop :=
  PsychicHabitsAreRelational ∧ PsychicVirtuesArePerfections ∧
    PsychicVicesAreDepartures ∧ PsychicVirtueDisposesWell ∧
    PsychicViceDisposesBadly ∧
    ¬ PsychicHabitsOrTheirAcquisitionOrLossAreAlterations

/-- Moral habits arise only while the sensitive part is altered, and that part is
altered by sensible things, in Aristotle, *Physics* VII.3, 247a5-7.

Source: Aristotle, *Physics* VII.3, 247a5-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MoralHabitsRequireSensitiveAlterationBySensiblesReading
    (MoralHabitsAriseWithSensitivePartAltered
      SensitivePartAlteredBySensibles : Prop) : Prop :=
  MoralHabitsAriseWithSensitivePartAltered ∧ SensitivePartAlteredBySensibles

/-- Ethical virtue concerns bodily pleasures and pains, whether they occur in
action, memory, or expectation, in Aristotle, *Physics* VII.3, 247a7-10.

Source: Aristotle, *Physics* VII.3, 247a7-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EthicalVirtueConcernsBodilyPleasurePainReading
    (EthicalVirtueConcernsBodilyPleasureAndPain : Prop) : Prop :=
  EthicalVirtueConcernsBodilyPleasureAndPain

/-- Pleasures in action occur through sensation, while pleasures in memory and
expectation derive from prior sensation—remembering what one underwent or
expecting what one will undergo—in Aristotle, *Physics* VII.3, 247a9-13.

Source: Aristotle, *Physics* VII.3, 247a9-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ActionMemoryExpectationPleasuresDependOnSensationReading
    (ActionMemoryExpectationPleasuresDependOnSensation : Prop) : Prop :=
  ActionMemoryExpectationPleasuresDependOnSensation

/-- All bodily pleasure of the kinds under discussion arises from sensible
things, in Aristotle, *Physics* VII.3, 247a12-13.

Source: Aristotle, *Physics* VII.3, 247a12-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BodilyPleasuresUnderDiscussionAriseFromSensiblesReading
    (BodilyPleasuresUnderDiscussionAriseFromSensibles : Prop) : Prop :=
  BodilyPleasuresUnderDiscussionAriseFromSensibles

/-- Virtue and vice arise with pleasure and pain, and those pleasures and pains
are alterations of the sensitive part, in Aristotle, *Physics* VII.3,
247a13-17.

Source: Aristotle, *Physics* VII.3, 247a13-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PleasurePainAlterSensitivePartAndHabitsAriseReading
    (PleasureAndPainAlterSensitivePart
      VirtueAndViceAriseWithPleasureAndPain : Prop) : Prop :=
  PleasureAndPainAlterSensitivePart ∧
    VirtueAndViceAriseWithPleasureAndPain

/-- From ethical virtue's concern with bodily pleasure and pain, the sensory
origin of those affections, and their alteration of the sensitive part, Aristotle
infers that moral habits arise with alteration but are not themselves alterations
in *Physics* VII.3, 247a7-19.

Source: Aristotle, *Physics* VII.3, 247a7-19 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SensoryAccountEntailsMoralHabitsWithAlterationReading
    (EthicalVirtueConcernsBodilyPleasureAndPain
      ActionMemoryExpectationPleasuresDependOnSensation
      BodilyPleasuresUnderDiscussionAriseFromSensibles
      PleasureAndPainAlterSensitivePart
      VirtueAndViceAriseWithPleasureAndPain
      MoralHabitsAriseWithSensitiveAlteration MoralHabitsAreAlterations : Prop) : Prop :=
  (EthicalVirtueConcernsBodilyPleasureAndPain ∧
      ActionMemoryExpectationPleasuresDependOnSensation ∧
      BodilyPleasuresUnderDiscussionAriseFromSensibles ∧
      PleasureAndPainAlterSensitivePart ∧
      VirtueAndViceAriseWithPleasureAndPain) →
    (MoralHabitsAriseWithSensitiveAlteration ∧ ¬ MoralHabitsAreAlterations)

/-- Moral habits arise with alteration of the sensitive part but are not
themselves alterations, in Aristotle, *Physics* VII.3, 247a13-19.

Source: Aristotle, *Physics* VII.3, 247a13-19 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MoralHabitsAriseWithAlterationButAreNotAlterationsReading
    (MoralHabitsAriseWithSensitiveAlteration MoralHabitsAreAlterations : Prop) : Prop :=
  MoralHabitsAriseWithSensitiveAlteration ∧ ¬ MoralHabitsAreAlterations

end TruthCore.Greek.Aristotle.Physics
