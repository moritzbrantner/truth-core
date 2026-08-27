import TruthCore.Greek.Aristotle.Physics.BookII.Chapter1

namespace TruthCore.Greek.Aristotle.Physics

/--
Opening problem in Aristotle, *Physics* II.2, 193b23-25: physicists and mathematicians both
study features such as surfaces, solids, lengths, and points found in physical bodies, so
their different modes of inquiry require determination.

Source: Aristotle, *Physics* II.2, 193b23-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PhysicsMathematicsSharePhysicalFeaturesReading
    (PhysicalBodiesHaveMathematicalFeatures
      PhysicistAndMathematicianStudySharedFeatures
      TheirModesOfInquiryRequireDistinction : Prop) : Prop :=
  PhysicalBodiesHaveMathematicalFeatures ∧
    PhysicistAndMathematicianStudySharedFeatures ∧
      TheirModesOfInquiryRequireDistinction

/--
Astronomical scope in Aristotle, *Physics* II.2, 193b25-31: it would be absurd for the
physicist to know what the sun or moon is while knowing none of its per se attributes;
writers on nature accordingly discuss celestial shape and the sphericity of earth and cosmos.

The claim records the subject-matter overlap without deciding whether astronomy is wholly a
part of physics in every later classification.

Source: Aristotle, *Physics* II.2, 193b25-31 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PhysicistStudiesCelestialPerSeAttributesReading
    (PhysicistKnowsCelestialNatures
      PhysicistKnowsNoCelestialPerSeAttributes
      NaturalInquiryStudiesCelestialShapes : Prop) : Prop :=
  (PhysicistKnowsCelestialNatures →
      ¬ PhysicistKnowsNoCelestialPerSeAttributes) ∧
    NaturalInquiryStudiesCelestialShapes

/--
Mathematical mode of inquiry in Aristotle, *Physics* II.2, 193b31-33: the mathematician
studies boundaries and their attributes, but not precisely qua boundaries or attributes of
physical bodies.

Source: Aristotle, *Physics* II.2, 193b31-33 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MathematicianStudiesFeaturesNotQuaPhysicalReading
    (MathematicianStudiesPhysicalBodyFeatures
      MathematicianStudiesThemQuaPhysical : Prop) : Prop :=
  MathematicianStudiesPhysicalBodyFeatures ∧
    ¬ MathematicianStudiesThemQuaPhysical

/--
Legitimacy of abstraction in Aristotle, *Physics* II.2, 193b33-35: mathematical objects are
separable from motion in thought, and separating them in that way introduces no falsehood.

The qualification “in thought” is retained; this is not ontological separability.

Source: Aristotle, *Physics* II.2, 193b33-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MathematicalAbstractionFromMotionLegitimateReading
    (MathematicalObjectsSeparableFromMotionInThought
      AbstractionFromMotionIntroducesFalsehood : Prop) : Prop :=
  MathematicalObjectsSeparableFromMotionInThought ∧
    ¬ AbstractionFromMotionIntroducesFalsehood

/--
Critique in Aristotle, *Physics* II.2, 193b35-194a1: advocates of separately existing Forms
unwittingly separate natural things even though natural things are less separable than
mathematical objects.

This is Aristotle's attributed criticism and does not identify every theory of forms with
the target of the passage.

Source: Aristotle, *Physics* II.2, 193b35-194a1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FormsTheorySeparatesLessSeparableNaturalThingsReading
    (FormsTheoristsSeparateNaturalThings
      NaturalThingsLessSeparableThanMathematicalObjects : Prop) : Prop :=
  FormsTheoristsSeparateNaturalThings ∧
    NaturalThingsLessSeparableThanMathematicalObjects

/--
First definition-based premise in Aristotle, *Physics* II.2, 194a1-7: odd, even, straight,
curved, number, line, and shape can be defined without motion.

Source: Aristotle, *Physics* II.2, 194a1-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MathematicalDefinitionsMotionIndependentReading
    (MathematicalDefinitionsRequireMotion : Prop) : Prop :=
  ¬ MathematicalDefinitionsRequireMotion

/--
Second definition-based premise in Aristotle, *Physics* II.2, 194a1-7: flesh, bone, and human
cannot be defined without motion, as snubness cannot be defined like curvature alone.

Source: Aristotle, *Physics* II.2, 194a1-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalDefinitionsMotionDependentReading
    (NaturalDefinitionsRequireMotion : Prop) : Prop :=
  NaturalDefinitionsRequireMotion

/--
Conclusion of the definition comparison in Aristotle, *Physics* II.2, 194a1-7: mathematical
and natural definitions differ in their dependence on motion.

Source: Aristotle, *Physics* II.2, 194a1-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DefinitionMotionDependenceDistinguishesInquiriesReading
    (MathematicalDefinitionsRequireMotion
      NaturalDefinitionsRequireMotion : Prop) : Prop :=
  ¬ MathematicalDefinitionsRequireMotion ∧
    NaturalDefinitionsRequireMotion

/--
Mixed mathematical sciences in Aristotle, *Physics* II.2, 194a7-12: geometry studies a
physical line not qua physical, whereas optics studies a mathematical line qua physical;
harmonics and astronomy exhibit the same more-physical orientation.

Source: Aristotle, *Physics* II.2, 194a7-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MixedMathematicalSciencesReverseGeometryReading
    (GeometryStudiesPhysicalLineNotQuaPhysical
      OpticsStudiesMathematicalLineQuaPhysical
      HarmonicsAndAstronomyAreMorePhysical : Prop) : Prop :=
  GeometryStudiesPhysicalLineNotQuaPhysical ∧
    OpticsStudiesMathematicalLineQuaPhysical ∧
      HarmonicsAndAstronomyAreMorePhysical

/--
Method for natural objects in Aristotle, *Physics* II.2, 194a12-15: because nature is both
form and matter, natural objects must be studied like snubness—neither apart from matter nor
in terms of matter alone.

Source: Aristotle, *Physics* II.2, 194a12-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalObjectsNeitherMatterFreeNorMatterOnlyReading
    (NatureIncludesFormAndMatter
      NaturalObjectsStudiedWithoutMatter
      NaturalObjectsStudiedByMatterAlone : Prop) : Prop :=
  NatureIncludesFormAndMatter ∧
    ¬ NaturalObjectsStudiedWithoutMatter ∧
      ¬ NaturalObjectsStudiedByMatterAlone

end TruthCore.Greek.Aristotle.Physics
