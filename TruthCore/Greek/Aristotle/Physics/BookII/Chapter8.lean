import TruthCore.Greek.Aristotle.Physics.BookII.Chapter7

namespace TruthCore.Greek.Aristotle.Physics

/--
Agenda and historical criticism in Aristotle, *Physics* II.8, 198b10-16: natural teleology
and the role of necessity require explanation because earlier thinkers reduce natural
outcomes to the necessary behavior of material qualities and only briefly mention such other
causes as Love, Strife, or Mind.

Source: Aristotle, *Physics* II.8, 198b10-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalTeleologyAndNecessityInquiryReading
    (NaturalTeleologyRequiresExplanation
      NaturalNecessityRequiresExplanation
      PredecessorsReduceOutcomesToMaterialNecessity
      PredecessorsDoNotDevelopOtherNamedCauses : Prop) : Prop :=
  NaturalTeleologyRequiresExplanation ∧
    NaturalNecessityRequiresExplanation ∧
      PredecessorsReduceOutcomesToMaterialNecessity ∧
        PredecessorsDoNotDevelopOtherNamedCauses

/--
Attributed objection in Aristotle, *Physics* II.8, 198b16-29: as rain falls from material
necessity rather than for crops, useful teeth and other apparently purposive parts might arise
necessarily, with their usefulness merely coincidental.

This is the objection Aristotle will answer, not his endorsed account.

Source: Aristotle, *Physics* II.8, 198b16-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AttributedMaterialNecessityCoincidenceObjectionReading
    (RainFallsFromMaterialNecessityNotForCrops
      CropBenefitOrDamageIsCoincidental
      TeethAriseFromNecessity
      ToothUsefulnessIsCoincidental
      OtherApparentlyPurposivePartsLikewise : Prop) : Prop :=
  RainFallsFromMaterialNecessityNotForCrops ∧
    CropBenefitOrDamageIsCoincidental ∧
      TeethAriseFromNecessity ∧
        ToothUsefulnessIsCoincidental ∧
          OtherApparentlyPurposivePartsLikewise

/--
Attributed continuation of the objection in Aristotle, *Physics* II.8, 198b29-32: organisms
whose parts happened to be suitably constituted survived spontaneously, while unsuitable
combinations perished, as in the Empedoclean human-faced ox progeny.

No endorsement or modern evolutionary reconstruction is implied.

Source: Aristotle, *Physics* II.8, 198b29-32 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AttributedSpontaneousSuitabilitySurvivalReading
    (SuitablyConstitutedCombinationsSurviveSpontaneously
      UnsuitableCombinationsPerish
      EmpedocleanHybridIllustratesFailure : Prop) : Prop :=
  SuitablyConstitutedCombinationsSurviveSpontaneously ∧
    UnsuitableCombinationsPerish ∧
      EmpedocleanHybridIllustratesFailure

/--
First premise of Aristotle's reply in *Physics* II.8, 198b34-199a3: natural things come to
be in the same way always or for the most part.

Source: Aristotle, *Physics* II.8, 198b34-199a3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalOutcomesAlwaysOrUsualReading
    (NaturalOutcomesAreAlwaysOrUsual : Prop) : Prop :=
  NaturalOutcomesAreAlwaysOrUsual

/--
Second premise of Aristotle's reply in *Physics* II.8, 198b34-199a3: chance and spontaneity
do not explain an always-or-for-the-most-part natural pattern; only exceptional seasonal
weather is attributed to coincidence.

Source: Aristotle, *Physics* II.8, 198b34-199a3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChanceSpontaneityDoNotExplainNaturalRegularityReading
    (NaturalRegularityIsChanceOrSpontaneous : Prop) : Prop :=
  ¬ NaturalRegularityIsChanceOrSpontaneous

/--
Inferential bridge in Aristotle's *Physics* II.8, 199a3-8: if natural outcomes are regular,
are not from chance or spontaneity, and the relevant alternatives are coincidence or an end,
then natural things are for an end.

Source: Aristotle, *Physics* II.8, 199a3-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalRegularityImpliesTeleologyReading
    (NaturalOutcomesAreAlwaysOrUsual NaturalRegularityIsChanceOrSpontaneous
      NaturalThingsActForEnds : Prop) : Prop :=
  NaturalOutcomesAreAlwaysOrUsual ∧ ¬ NaturalRegularityIsChanceOrSpontaneous →
    NaturalThingsActForEnds

/--
Conclusion of Aristotle's regularity argument in *Physics* II.8, 199a7-8: acting for an end
is present among things that come to be and exist by nature.

Source: Aristotle, *Physics* II.8, 199a7-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalThingsActForEndsReading (NaturalThingsActForEnds : Prop) : Prop :=
  NaturalThingsActForEnds

/--
Art/nature analogy in Aristotle, *Physics* II.8, 199a8-17: if a house arose by nature its
stages would follow the order used by craft, and if natural products arose by craft they
would follow their natural order. Craft completes what nature cannot and imitates nature;
the parallel ordering supports final causation in nature as in craft.

Source: Aristotle, *Physics* II.8, 199a8-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ArtNatureParallelSupportsTeleologyReading
    (NaturalAndCraftProcessesHaveParallelOrder
      CraftCompletesSomeNaturalWork
      CraftImitatesNature
      CraftedThingsActForEnds
      ParallelSupportsNaturalTeleology : Prop) : Prop :=
  NaturalAndCraftProcessesHaveParallelOrder ∧
    CraftCompletesSomeNaturalWork ∧
      CraftImitatesNature ∧
        CraftedThingsActForEnds ∧
          ParallelSupportsNaturalTeleology

/--
Non-deliberative teleology in Aristotle, *Physics* II.8, 199a17-30: animals such as spiders,
ants, and swallows, and plants through leaves and downward roots, produce end-directed
structures without inquiry or deliberation.

The examples show that deliberation is not required for natural purposiveness; they do not
attribute human reasoning to animals or plants.

Source: Aristotle, *Physics* II.8, 199a17-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AnimalsPlantsPurposiveWithoutDeliberationReading
    (SomeAnimalsDoNotInquireOrDeliberate
      SomeAnimalsProduceEndDirectedStructures
      PlantsProduceStructuresBeneficialForEnds
      NaturalPurposivenessRequiresDeliberation : Prop) : Prop :=
  SomeAnimalsDoNotInquireOrDeliberate ∧
    SomeAnimalsProduceEndDirectedStructures ∧
      PlantsProduceStructuresBeneficialForEnds ∧
        ¬ NaturalPurposivenessRequiresDeliberation

/--
Form/final-cause identification in Aristotle, *Physics* II.8, 199a30-32: nature is said as
matter and as form; form is the end, and other stages are for that end, so formal nature is
the final cause in this explanatory relation.

Source: Aristotle, *Physics* II.8, 199a30-32 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FormalNatureServesAsFinalCauseReading
    (NatureSaidAsMatterAndForm
      FormIsEnd
      OtherStagesAreForForm
      FormalNatureIsFinalCause : Prop) : Prop :=
  NatureSaidAsMatterAndForm ∧
    FormIsEnd ∧
      OtherStagesAreForForm ∧
        FormalNatureIsFinalCause

/--
First premise of Aristotle's error analogy in *Physics* II.8, 199a33-199b4: grammarians and
doctors can perform their arts incorrectly even though correct practice is for an end.

Source: Aristotle, *Physics* II.8, 199a33-199b4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ArtCanFailWhileAimingAtEndReading
    (ArtAimsAtEnds ArtCanFailToReachItsEnd : Prop) : Prop :=
  ArtAimsAtEnds ∧ ArtCanFailToReachItsEnd

/--
Inferential bridge in Aristotle's *Physics* II.8, 199a33-199b4: if art can fail while aiming
at an end and natural processes are analogous in this respect, then natural errors are
compatible with natural teleology.

Source: Aristotle, *Physics* II.8, 199a33-199b4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ArtNatureErrorAnalogyReading
    (ArtCanFailWhileAimingAtEnd NaturalErrorsCompatibleWithTeleology : Prop) : Prop :=
  ArtCanFailWhileAimingAtEnd → NaturalErrorsCompatibleWithTeleology

/--
Conclusion of Aristotle's error analogy in *Physics* II.8, 199b1-4: natural processes can
miss their ends, and monsters are errors relative to the end rather than evidence that no end
was operative.

Source: Aristotle, *Physics* II.8, 199b1-4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalErrorsCompatibleWithTeleologyReading
    (NaturalErrorsCompatibleWithTeleology : Prop) : Prop :=
  NaturalErrorsCompatibleWithTeleology

/--
Application of the error account in Aristotle, *Physics* II.8, 199b1-4: monsters are natural
failures relative to the end, not evidence that natural generation lacks ends altogether.

Source: Aristotle, *Physics* II.8, 199b1-4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MonstersAreFailuresRelativeToNaturalEndReading
    (MonstersAreFailuresRelativeToNaturalEnd : Prop) : Prop :=
  MonstersAreFailuresRelativeToNaturalEnd

/--
Reply to the Empedoclean hybrid in Aristotle, *Physics* II.8, 199b4-9: if primordial hybrids
failed to reach a determinate limit and end, they arose through corruption of an originating
principle, analogously to present failures caused by corrupted seed.

Source: Aristotle, *Physics* II.8, 199b4-9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PrimordialHybridsAsCorruptedDevelopmentReading
    (PrimordialHybridsFailedDeterminateEnd
      FailureCameFromCorruptedOriginatingPrinciple
      PresentCorruptedSeedIsAnalogous : Prop) : Prop :=
  PrimordialHybridsFailedDeterminateEnd ∧
    FailureCameFromCorruptedOriginatingPrinciple ∧
      PresentCorruptedSeedIsAnalogous

/--
Developmental-order reply in Aristotle, *Physics* II.8, 199b9-13: seed must precede the
completed animal; Empedocles' “whole-natured first” is therefore treated as seed rather than
an immediately complete organism.

Source: Aristotle, *Physics* II.8, 199b9-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SeedPrecedesCompletedOrganismReading
    (SeedPrecedesCompletedOrganism
      EmpedocleanWholeNaturedFirstWasSeed : Prop) : Prop :=
  SeedPrecedesCompletedOrganism ∧ EmpedocleanWholeNaturedFirstWasSeed

/--
Plant-and-seed reductio in Aristotle, *Physics* II.8, 199b13-18: since purposiveness also
appears in plants, a random-combination account would require analogous plant hybrids and
random outcomes in seeds; Aristotle rejects those consequences.

Source: Aristotle, *Physics* II.8, 199b13-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PlantSeedRandomnessReductioReading
    (RandomAccountRequiresPlantHybrids
      RandomAccountRequiresIndeterminateSeedOutcomes
      PlantHybridsAndIndeterminateSeedsAccepted : Prop) : Prop :=
  RandomAccountRequiresPlantHybrids ∧
    RandomAccountRequiresIndeterminateSeedOutcomes ∧
      ¬ PlantHybridsAndIndeterminateSeedsAccepted

/--
Definition and criticism in Aristotle, *Physics* II.8, 199b18-26: natural things move
continuously from an internal principle toward a determinate end, reaching the same outcome
unless impeded. Treating this sequence as random abolishes both natural things and nature.

Source: Aristotle, *Physics* II.8, 199b18-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InternalPrincipleDeterminateEndDefinesNatureReading
    (NaturalThingsMoveContinuouslyFromInternalPrinciple
      NaturalMotionReachesDeterminateEnd
      SameOutcomeOccursUnlessImpeded
      RandomAccountAbolishesNature : Prop) : Prop :=
  NaturalThingsMoveContinuouslyFromInternalPrinciple ∧
    NaturalMotionReachesDeterminateEnd ∧
      SameOutcomeOccursUnlessImpeded ∧
        RandomAccountAbolishesNature

/--
Chance qualification in Aristotle, *Physics* II.8, 199b26-28: an event can incidentally
appear to occur for an end by chance, but what occurs always or for the most part in natural
processes is neither incidental nor from chance.

Source: Aristotle, *Physics* II.8, 199b26-28 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ApparentEndByChanceOnlyIncidentallyReading
    (ChanceCanIncidentallyAppearForEnd
      RegularNaturalOutcomeIsIncidentalOrChance : Prop) : Prop :=
  ChanceCanIncidentallyAppearForEnd ∧
    ¬ RegularNaturalOutcomeIsIncidentalOrChance

/--
Anti-deliberation reply in Aristotle, *Physics* II.8, 199b28-32: failure to observe a
deliberating mover does not remove final causation. Art itself does not deliberate, and if
shipbuilding were internal to wood it would produce as nature does; self-healing supplies the
closest analogy.

Source: Aristotle, *Physics* II.8, 199b28-32 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TeleologyDoesNotRequireDeliberatingMoverReading
    (ObservedDeliberatingMoverRequiredForTeleology
      ArtItselfDeliberates
      InternalShipbuildingWouldActLikeNature
      SelfHealingAnalogousToNature : Prop) : Prop :=
  ¬ ObservedDeliberatingMoverRequiredForTeleology ∧
    ¬ ArtItselfDeliberates ∧
      InternalShipbuildingWouldActLikeNature ∧
        SelfHealingAnalogousToNature

end TruthCore.Greek.Aristotle.Physics
