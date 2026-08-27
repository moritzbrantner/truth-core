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

end TruthCore.Greek.Aristotle.Physics
