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

/--
Scope question in Aristotle, *Physics* II.2, 194a15-18: because the physicist studies the
compound of matter and form, physical inquiry must know each of those two natures as well.

Source: Aristotle, *Physics* II.2, 194a15-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PhysicistStudiesCompoundMatterAndFormReading
    (PhysicistStudiesMatterFormCompound
      PhysicistStudiesMatter
      PhysicistStudiesForm : Prop) : Prop :=
  PhysicistStudiesMatterFormCompound ∧
    PhysicistStudiesMatter ∧
      PhysicistStudiesForm

/--
Historical assessment in Aristotle, *Physics* II.2, 194a18-21: the earlier investigators
make physics appear chiefly concerned with matter because Empedocles and Democritus touched
form and essence only to a small extent.

This is an attributed assessment, not a claim that their work contains no formal explanation.

Source: Aristotle, *Physics* II.2, 194a18-21 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AncientsMostlyInvestigateMatterReading
    (AncientsMostlyInvestigateMatter
      EmpedoclesDemocritusInvestigateNoFormOrEssence : Prop) : Prop :=
  AncientsMostlyInvestigateMatter ∧
    ¬ EmpedoclesDemocritusInvestigateNoFormOrEssence

/-- First premise in Aristotle's *Physics* II.2, 194a21-27 craft analogy: art imitates nature. -/
def ArtImitatesNatureReading (ArtImitatesNature : Prop) : Prop :=
  ArtImitatesNature

/--
Second premise in Aristotle's *Physics* II.2, 194a21-27 craft analogy: one craft knows both
its form and, up to the relevant limit, the matter in which that form is realized, as medicine
knows health and bodily materials and building knows house-form and bricks or wood.

Source: Aristotle, *Physics* II.2, 194a21-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CraftKnowsFormAndMatterUpToPointReading
    (OneCraftKnowsFormAndMatterUpToPoint : Prop) : Prop :=
  OneCraftKnowsFormAndMatterUpToPoint

/--
Inferential bridge in Aristotle's *Physics* II.2, 194a21-27: if art imitates nature and one
craft knows both form and matter to the appropriate extent, then physics likewise knows both
senses of nature.

Source: Aristotle, *Physics* II.2, 194a21-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CraftAnalogyTransfersMatterFormKnowledgeReading
    (ArtImitatesNature OneCraftKnowsFormAndMatterUpToPoint
      PhysicsKnowsMatterAndForm : Prop) : Prop :=
  ArtImitatesNature ∧ OneCraftKnowsFormAndMatterUpToPoint →
    PhysicsKnowsMatterAndForm

/--
Conclusion of the craft analogy in Aristotle, *Physics* II.2, 194a21-27: physical science
knows both matter and form.

Source: Aristotle, *Physics* II.2, 194a21-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PhysicsKnowsMatterAndFormReading
    (PhysicsKnowsMatterAndForm : Prop) : Prop :=
  PhysicsKnowsMatterAndForm

/--
Teleological scope in Aristotle, *Physics* II.2, 194a27-33: end and means belong to the same
discipline; nature is an end and that for the sake of which, where an end is not merely the
last stage of a continuous change but the best completion.

Source: Aristotle, *Physics* II.2, 194a27-33 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NatureAsBestEndAndForSakeOfReading
(EndAndMeansBelongToSameDiscipline
      NatureIsEndAndForSakeOf
      EveryLastStageIsEnd
      EndIsBestRatherThanMerelyLast : Prop) : Prop :=
  EndAndMeansBelongToSameDiscipline ∧
    NatureIsEndAndForSakeOf ∧
      ¬ EveryLastStageIsEnd ∧
        EndIsBestRatherThanMerelyLast

/--
Matter for function in Aristotle, *Physics* II.2, 194a33-194b8: crafts make or render their
matter serviceable for the work, whereas in natural things matter is already present.

Source: Aristotle, *Physics* II.2, 194a33-194b8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ArtMakesMatterForFunctionNatureHasMatterReading
    (ArtMakesOrPreparesMatterForFunction
      NaturalThingsHaveMatterAlreadyPresent : Prop) : Prop :=
  ArtMakesOrPreparesMatterForFunction ∧
    NaturalThingsHaveMatterAlreadyPresent

/--
Directive arts in Aristotle, *Physics* II.2, 194a33-194b8: the using art and the
architectonic productive art both govern matter but differ in knowledge—the user knows and
prescribes form, while the productive director knows the matter and operations.

Source: Aristotle, *Physics* II.2, 194a33-194b8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def UsingAndProductiveArtsDivideFormMatterKnowledgeReading
    (UsingAndProductiveArtsGovernMatter
      UsingArtKnowsAndPrescribesForm
      ProductiveArtKnowsMatterAndOperations : Prop) : Prop :=
  UsingAndProductiveArtsGovernMatter ∧
    UsingArtKnowsAndPrescribesForm ∧
      ProductiveArtKnowsMatterAndOperations

/--
Relativity of matter in Aristotle, *Physics* II.2, 194b8-9: matter is relative, since a
different form has a different appropriate matter.

Source: Aristotle, *Physics* II.2, 194b8-9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MatterRelativeToFormReading
    (MatterIsRelative DifferentFormHasDifferentMatter : Prop) : Prop :=
  MatterIsRelative ∧ DifferentFormHasDifferentMatter

/--
Boundary of physical inquiry in Aristotle, *Physics* II.2, 194b9-15: the physicist knows
form and essence up to the purpose of each natural thing and studies forms separable in
account but present in matter; the mode of existence and essence of what is separable belongs
to first philosophy.

The passage's human-and-sun remark is not expanded into a general causal doctrine here.

Source: Aristotle, *Physics* II.2, 194b9-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PhysicsFormKnowledgeLimitedByPurposeReading
    (PhysicistKnowsFormAndEssenceUpToPurpose
      PhysicalFormsSeparableInAccountButInMatter
      SeparablesBelongToFirstPhilosophy : Prop) : Prop :=
  PhysicistKnowsFormAndEssenceUpToPurpose ∧
    PhysicalFormsSeparableInAccountButInMatter ∧
      SeparablesBelongToFirstPhilosophy

end TruthCore.Greek.Aristotle.Physics
