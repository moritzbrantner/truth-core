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

end TruthCore.Greek.Aristotle.Physics
