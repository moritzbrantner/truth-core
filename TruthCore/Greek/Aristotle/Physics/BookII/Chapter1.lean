import TruthCore.Greek.Aristotle.Physics.BookI.Chapter9

namespace TruthCore.Greek.Aristotle.Physics

/--
Opening contrast in Aristotle, *Physics* II.1, 192b8-20: natural things have an internal
principle of motion and rest, while artifacts have no innate impulse to change precisely qua
artifact. An artifact can nevertheless have such an impulse insofar as its material is
natural.

The qualifications prevent the natural/artificial distinction from becoming the false claim
that an artifact's materials have no natural tendencies.

Source: Aristotle, *Physics* II.1, 192b8-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalArtificialChangePrincipleContrastReading
    (NaturalThingsHaveInternalMotionRestPrinciple
      ArtifactsHaveInnateChangeImpulseQuaArtifact
      ArtifactsHaveNaturalImpulseQuaMaterial : Prop) : Prop :=
  NaturalThingsHaveInternalMotionRestPrinciple ∧
    ¬ ArtifactsHaveInnateChangeImpulseQuaArtifact ∧
      ArtifactsHaveNaturalImpulseQuaMaterial

/--
Definition in Aristotle, *Physics* II.1, 192b20-32: nature is a source and cause of motion
and rest in that to which it belongs primarily, in virtue of itself and not incidentally.

The doctor who happens to heal himself and artifacts whose productive source is external or
only incidentally internal explain the final qualification; they are not generalized into a
theory of every kind of causation.

Source: Aristotle, *Physics* II.1, 192b20-32 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NatureInternalPerSeMotionRestCauseReading
    (NatureIsMotionRestCause BelongsPrimarilyInSubject
      BelongsInVirtueOfItself BelongsIncidentally : Prop) : Prop :=
  NatureIsMotionRestCause ∧
    BelongsPrimarilyInSubject ∧
      BelongsInVirtueOfItself ∧
        ¬ BelongsIncidentally

/--
Subject claim in Aristotle, *Physics* II.1, 192b32-35: things which have the specified
principle have a nature and are substances, because each is a subject and nature is always in
a subject.

Source: Aristotle, *Physics* II.1, 192b32-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ThingsHavingNatureAreSubstancesAndSubjectsReading
    (ThingsWithSpecifiedPrincipleHaveNature
      ThingsHavingNatureAreSubstances
      EachSuchThingIsSubject
      NatureIsAlwaysInSubject : Prop) : Prop :=
  ThingsWithSpecifiedPrincipleHaveNature ∧
    ThingsHavingNatureAreSubstances ∧
      EachSuchThingIsSubject ∧
        NatureIsAlwaysInSubject

/--
Terminological distinction in Aristotle, *Physics* II.1, 192b35-193a1: “according to
nature” applies both to natural things and to attributes belonging to them in virtue of what
they are, even though such an attribute is not itself a nature and does not have a nature.

Source: Aristotle, *Physics* II.1, 192b35-193a1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AccordingToNatureIncludesPerSeAttributesReading
    (NaturalThingsAreAccordingToNature
      PerSeAttributesAreAccordingToNature
      PerSeAttributeIsNature
      PerSeAttributeHasNature : Prop) : Prop :=
  NaturalThingsAreAccordingToNature ∧
    PerSeAttributesAreAccordingToNature ∧
      ¬ PerSeAttributeIsNature ∧
        ¬ PerSeAttributeHasNature

/--
Methodological claim in Aristotle, *Physics* II.1, 193a3-9: the existence of nature is
evident from the many things of the specified kind, so attempting to prove it through what
is less evident reverses the appropriate order of knowledge.

Source: Aristotle, *Physics* II.1, 193a3-9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NatureExistsWithoutProofFromLessEvidentReading
    (NatureExists NatureRequiresProofFromLessEvident : Prop) : Prop :=
  NatureExists ∧ ¬ NatureRequiresProofFromLessEvident

/--
Attributed material account in Aristotle, *Physics* II.1, 193a9-17: some identify the
nature or substance of a thing with its first inherent, unarranged material constituent,
treating its art-produced arrangement as incidental.

This is recorded as a predecessor view rather than Aristotle's final preference between
matter and form.

Source: Aristotle, *Physics* II.1, 193a9-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AttributedImmediateMatterNatureReading
    (ImmediateUnarrangedMaterialIsNature
      ImmediateUnarrangedMaterialIsSubstance
      ArtificialArrangementIsNature : Prop) : Prop :=
  ImmediateUnarrangedMaterialIsNature ∧
    ImmediateUnarrangedMaterialIsSubstance ∧
      ¬ ArtificialArrangementIsNature

/--
Antiphon's evidence in Aristotle, *Physics* II.1, 193a12-17: if a buried bed's decaying
material acquired the power to sprout, what emerged would be wood rather than a bed.

The antecedent remains hypothetical; the statement does not claim that beds actually sprout.

Source: Aristotle, *Physics* II.1, 193a12-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AntiphonBedSproutingEvidenceReading
    (BedMaterialSprouts WoodEmerges BedEmerges : Prop) : Prop :=
  BedMaterialSprouts → WoodEmerges ∧ ¬ BedEmerges

/--
Attributed evidential step in Aristotle, *Physics* II.1, 193a12-17: the hypothetical
emergence of wood rather than bed-form is taken to show that the enduring material is nature
and the art-produced arrangement is not nature in its own right.

Source: Aristotle, *Physics* II.1, 193a12-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AntiphonSproutingSupportsMaterialNatureReading
    (WoodEmerges BedEmerges MaterialIsNature ArtificialArrangementIsNature : Prop) : Prop :=
  WoodEmerges ∧ ¬ BedEmerges →
    MaterialIsNature ∧ ¬ ArtificialArrangementIsNature

/--
Conditional conclusion of Antiphon's evidence in Aristotle, *Physics* II.1, 193a12-17: if
the buried bed's material sprouts, the material rather than the artificial arrangement is
treated as nature.

Source: Aristotle, *Physics* II.1, 193a12-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AntiphonMaterialNatureConclusionReading
    (BedMaterialSprouts MaterialIsNature ArtificialArrangementIsNature : Prop) : Prop :=
  BedMaterialSprouts →
    MaterialIsNature ∧ ¬ ArtificialArrangementIsNature

/--
Attributed regress to elements in Aristotle, *Physics* II.1, 193a17-28: thinkers who apply
the same material relation repeatedly identify one or more elements as the whole underlying
substance, regard other things as their affections or dispositions, and take the elements as
eternal while the other things repeatedly come to be and perish.

Source: Aristotle, *Physics* II.1, 193a17-28 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AttributedElementsAsUltimateNatureReading
    (OneOrMoreElementsAreWholeSubstance
      OtherThingsAreElementAffections
      ElementsAreEternal
      OtherThingsRepeatedlyComeToBeAndPerish : Prop) : Prop :=
  OneOrMoreElementsAreWholeSubstance ∧
    OtherThingsAreElementAffections ∧
      ElementsAreEternal ∧
        OtherThingsRepeatedlyComeToBeAndPerish

/--
Material sense of nature in Aristotle, *Physics* II.1, 193a28-30: nature is said in one way
as the primary matter underlying each thing that has an internal principle of motion and
change.

Source: Aristotle, *Physics* II.1, 193a28-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PrimaryMatterAsNatureReading
    (PrimaryUnderlyingMatterIsNature
      ThingsHaveInternalMotionChangePrinciple : Prop) : Prop :=
  PrimaryUnderlyingMatterIsNature ∧
    ThingsHaveInternalMotionChangePrinciple

/--
Formal sense of nature in Aristotle, *Physics* II.1, 193a30-193b5: nature is also the shape
or form specified in a thing's definition, separable from the natural compound only in
account.

The final qualification blocks a claim that the form is separately existing.

Source: Aristotle, *Physics* II.1, 193a30-193b5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DefinitionalFormAsNatureReading
    (DefinitionalFormIsNature FormIsSeparableBeyondAccount : Prop) : Prop :=
  DefinitionalFormIsNature ∧ ¬ FormIsSeparableBeyondAccount

/--
Potential-material qualification in Aristotle, *Physics* II.1, 193a31-193b5: what is only
potentially flesh or bone does not yet have its own nature and is not yet by nature before
receiving the form specified in its definition.

Source: Aristotle, *Physics* II.1, 193a31-193b5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PotentialFleshBoneNotYetNatureReading
    (PotentialFleshBoneHasOwnNatureBeforeForm
      PotentialFleshBoneIsByNatureBeforeForm : Prop) : Prop :=
  ¬ PotentialFleshBoneHasOwnNatureBeforeForm ∧
    ¬ PotentialFleshBoneIsByNatureBeforeForm

/--
Compound qualification in Aristotle, *Physics* II.1, 193b3-5: the compound of matter and
form, such as a human being, is not itself a nature but is by nature or natural.

Source: Aristotle, *Physics* II.1, 193b3-5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalCompoundIsByNatureNotNatureReading
    (NaturalCompoundIsNature NaturalCompoundIsByNature : Prop) : Prop :=
  ¬ NaturalCompoundIsNature ∧ NaturalCompoundIsByNature

/--
Priority claim in Aristotle, *Physics* II.1, 193b6-8: form is nature more than matter is,
because a thing is called what it is more when actual than when potential.

This records the comparative “more” and does not deny that matter is nature in the sense
just established at 193a28-30.

Source: Aristotle, *Physics* II.1, 193b6-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FormMoreNatureThanMatterReading
    (ThingNamedMoreByActualityThanPotentiality
      FormIsNatureMoreThanMatter : Prop) : Prop :=
  ThingNamedMoreByActualityThanPotentiality ∧
    FormIsNatureMoreThanMatter

/--
Same-kind generation argument in Aristotle, *Physics* II.1, 193b8-12: a human comes from a
human while a bed does not come from a bed; this supports form, as well as the material in
the reported bed example, being nature.

The statement does not claim that every natural generation is univocal in every respect.

Source: Aristotle, *Physics* II.1, 193b8-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SameKindGenerationSupportsFormNatureReading
    (HumanComesFromHuman BedComesFromBed FormIsNature : Prop) : Prop :=
  HumanComesFromHuman ∧ ¬ BedComesFromBed → FormIsNature

/--
First premise of Aristotle's growth argument in *Physics* II.1, 193b12-18: nature spoken of
as generation or growth is a path into nature, unlike doctoring, which proceeds from the art
of medicine toward health.

Source: Aristotle, *Physics* II.1, 193b12-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GrowthAsPathIntoNatureReading (GrowthReachesNature : Prop) : Prop :=
  GrowthReachesNature

/--
Second premise of Aristotle's growth argument in *Physics* II.1, 193b12-18: what grows moves
toward its form, not toward the material source from which it began.

Source: Aristotle, *Physics* II.1, 193b12-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GrowingTerminatesInFormNotMaterialReading
    (GrowthReachesForm GrowthReachesMaterialSource : Prop) : Prop :=
  GrowthReachesForm ∧ ¬ GrowthReachesMaterialSource

/--
Conclusion of Aristotle's growth argument in *Physics* II.1, 193b12-18: the target of growth
is both form and nature, so the form attained through growth is nature.

The proposition variables preserve the passage's target-relative conclusion rather than
universalizing it to every later notion called form.

Source: Aristotle, *Physics* II.1, 193b12-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GrowthTargetIsFormAndNatureReading
    (GrowthReachesForm GrowthReachesNature : Prop) : Prop :=
  GrowthReachesForm ∧ GrowthReachesNature

/--
Closing qualification in Aristotle, *Physics* II.1, 193b18-22: form and nature are said in
two ways because privation too is form in a qualified sense; whether privation is a contrary
in unqualified generation is deferred.

Source: Aristotle, *Physics* II.1, 193b18-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PrivationQualifiedFormQuestionDeferredReading
    (FormAndNatureSaidInTwoWays
      PrivationIsFormInQualifiedSense
      PrivationContraryQuestionResolved : Prop) : Prop :=
  FormAndNatureSaidInTwoWays ∧
    PrivationIsFormInQualifiedSense ∧
      ¬ PrivationContraryQuestionResolved

end TruthCore.Greek.Aristotle.Physics
