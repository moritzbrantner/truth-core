import TruthCore.Greek.Aristotle.Physics.BookII.Chapter2

namespace TruthCore.Greek.Aristotle.Physics

/--
Methodological application in Aristotle, *Physics* II.3, 194b16-23: knowledge of generation,
destruction, and every natural change requires grasping the relevant “why,” namely the first
cause, so physical questions should be referred to their causal principles.

This is narrower than the general I.1 statement about principles, causes, and elements: it
specifically applies primary-cause inquiry to natural change.

Source: Aristotle, *Physics* II.3, 194b16-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def KnowledgeOfNaturalChangeRequiresPrimaryCauseReading
    (KnowledgeOfNaturalChange RequiresGraspOfWhyAndPrimaryCause
      PhysicalQuestionsReferredToCausalPrinciples : Prop) : Prop :=
  KnowledgeOfNaturalChange →
    RequiresGraspOfWhyAndPrimaryCause ∧
      PhysicalQuestionsReferredToCausalPrinciples

/--
Final-cause extension in Aristotle, *Physics* II.3, 194b32-195a3: intermediate activities
and instruments brought about toward an end are also for the sake of that end, though
activities and instruments differ from one another.

This supplements, rather than duplicates, the existing four-mode classification claim.

Source: Aristotle, *Physics* II.3, 194b32-195a3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FinalCauseIncludesIntermediateMeansReading
    (IntermediateActivitiesAreForEnd
      IntermediateInstrumentsAreForEnd
      ActivitiesAndInstrumentsDiffer : Prop) : Prop :=
  IntermediateActivitiesAreForEnd ∧
    IntermediateInstrumentsAreForEnd ∧
      ActivitiesAndInstrumentsDiffer

/--
First premise in Aristotle's *Physics* II.3, 195a3-8 inference: cause is said in several
modes.

Source: Aristotle, *Physics* II.3, 195a3-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CausesSaidInSeveralModesReading (CausesHaveSeveralModes : Prop) : Prop :=
  CausesHaveSeveralModes

/--
Inferential bridge in Aristotle's *Physics* II.3, 195a3-8: if cause is said in several modes,
one effect may have several proper causes in different modes.

Source: Aristotle, *Physics* II.3, 195a3-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SeveralModesPermitMultipleProperCausesReading
    (CausesHaveSeveralModes OneEffectHasMultipleProperCauses : Prop) : Prop :=
  CausesHaveSeveralModes → OneEffectHasMultipleProperCauses

/--
Conclusion in Aristotle, *Physics* II.3, 195a3-8: one effect can have several proper causes
in different modes, as bronze and sculpting craft cause the statue respectively as matter and
source of change.

Source: Aristotle, *Physics* II.3, 195a3-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def OneEffectMultipleProperCausesReading
    (OneEffectHasMultipleProperCauses : Prop) : Prop :=
  OneEffectHasMultipleProperCauses

/--
Reciprocal causation in Aristotle, *Physics* II.3, 195a8-10: some things cause one another,
as exercise causes fitness as a source of change while fitness causes exercise as an end;
the reciprocal causal roles are not of the same mode.

Source: Aristotle, *Physics* II.3, 195a8-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ReciprocalCausesDifferInModeReading
    (EffectsCanCauseOneAnother
      FirstCausesSecondAsSourceOfChange
      SecondCausesFirstAsEnd
      ReciprocalRolesHaveSameMode : Prop) : Prop :=
  EffectsCanCauseOneAnother ∧
    FirstCausesSecondAsSourceOfChange ∧
      SecondCausesFirstAsEnd ∧
        ¬ ReciprocalRolesHaveSameMode

/--
Presence/absence causation in Aristotle, *Physics* II.3, 195a10-15: something whose presence
causes one result may by its absence be blamed for the contrary, as a pilot's presence causes
safety while the pilot's absence causes the wreck.

Source: Aristotle, *Physics* II.3, 195a10-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PresenceAbsenceCauseContraryOutcomesReading
    (PresenceCausesOutcome AbsenceCausesContraryOutcome : Prop) : Prop :=
  PresenceCausesOutcome ∧ AbsenceCausesContraryOutcome

/--
Expanded examples in Aristotle, *Physics* II.3, 195a15-26: letters, materials, parts, and
premises exemplify the from-which mode; whole, composition, and form exemplify essence;
seed, doctor, adviser, and maker exemplify source of change; end and good exemplify that for
the sake of which.

The examples refine the already-reused four-causes statement without creating another
identity for the exhaustive classification itself.

Source: Aristotle, *Physics* II.3, 195a15-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FourCauseModesExpandedExamplesReading
    (LettersMaterialsPartsPremisesAreFromWhichCauses
      WholeCompositionFormAreEssenceCauses
      SeedDoctorAdviserMakerAreSourcesOfChange
      EndAndGoodAreFinalCauses : Prop) : Prop :=
  LettersMaterialsPartsPremisesAreFromWhichCauses ∧
    WholeCompositionFormAreEssenceCauses ∧
      SeedDoctorAdviserMakerAreSourcesOfChange ∧
        EndAndGoodAreFinalCauses

/--
Final-cause qualification in Aristotle, *Physics* II.3, 195a23-26: that for the sake of
which is treated as best and as end for the preceding means, whether it is called the good
itself or the apparent good.

This records Aristotle's stated indifference between those descriptions here; it does not
identify apparent good with genuine good in every respect.

Source: Aristotle, *Physics* II.3, 195a23-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FinalCauseGoodOrApparentGoodReading
    (FinalCauseIsBestAndEnd
      GoodAndApparentGoodBothServeThisDescription : Prop) : Prop :=
  FinalCauseIsBestAndEnd ∧
    GoodAndApparentGoodBothServeThisDescription

/--
Priority within a causal kind in Aristotle, *Physics* II.3, 195a27-32: even causes of the
same kind may be prior or posterior, with more inclusive and more particular descriptions,
as expert and doctor or number and double ratio.

Source: Aristotle, *Physics* II.3, 195a27-32 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SameKindCausesPriorPosteriorInclusiveParticularReading
    (SameKindCausesCanBePriorOrPosterior
      CauseCanBeMoreInclusiveOrParticular : Prop) : Prop :=
  SameKindCausesCanBePriorOrPosterior ∧
    CauseCanBeMoreInclusiveOrParticular

/--
Incidental causation in Aristotle, *Physics* II.3, 195a32-195b3: Polyclitus causes a statue
incidentally insofar as Polyclitus happens to be the sculptor; incidental causes also have
genera and can be nearer to or more remote from the effect.

Source: Aristotle, *Physics* II.3, 195a32-195b3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IncidentalCausesHaveGeneraAndRemotenessReading
    (NamedIndividualIsCauseIncidentally
      IncidentalCausesHaveGenera
      IncidentalCausesVaryInRemoteness : Prop) : Prop :=
  NamedIndividualIsCauseIncidentally ∧
    IncidentalCausesHaveGenera ∧
      IncidentalCausesVaryInRemoteness

/--
Potential/actual distinction in Aristotle, *Physics* II.3, 195b3-6: every proper and
incidental cause may be described either as able to act or as actually acting, as builder or
builder building.

Source: Aristotle, *Physics* II.3, 195b3-6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ProperIncidentalCausesPotentialOrActualReading
    (ProperCausesPotentialOrActual
      IncidentalCausesPotentialOrActual : Prop) : Prop :=
  ProperCausesPotentialOrActual ∧
    IncidentalCausesPotentialOrActual

/--
Description of effects and causes in Aristotle, *Physics* II.3, 195b6-12: effects, their
materials, and incidental attributes may be named at particular or more generic levels, and
cause descriptions may be compounded, as “Polyclitus the sculptor.”

Source: Aristotle, *Physics* II.3, 195b6-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CausalDescriptionsVaryAndCanBeCompoundedReading
    (EffectsCanBeParticularOrGeneric
      MaterialsCanBeParticularOrGeneric
      IncidentalDescriptionsVaryLikewise
      CauseDescriptionsCanBeCompounded : Prop) : Prop :=
  EffectsCanBeParticularOrGeneric ∧
    MaterialsCanBeParticularOrGeneric ∧
      IncidentalDescriptionsVaryLikewise ∧
        CauseDescriptionsCanBeCompounded

/--
Sixfold summary in Aristotle, *Physics* II.3, 195b12-16: cause may be particular, generic,
incidental, a genus of the incidental, a compound of these, or simply stated; every one is
then said either actually or potentially.

Source: Aristotle, *Physics* II.3, 195b12-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SixCausalDescriptionModesTwofoldReading
    (SixCausalDescriptionModes
      EveryModeActualOrPotential : Prop) : Prop :=
  SixCausalDescriptionModes ∧ EveryModeActualOrPotential

/--
Temporal difference in Aristotle, *Physics* II.3, 195b16-21: an actually operating
particular cause exists and ceases together with the effect it is producing, whereas a
potential cause need not cease together with the effect.

This is restricted to the actual-particular and potential contrast made in the passage.

Source: Aristotle, *Physics* II.3, 195b16-21 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ActualParticularCauseCoevalPotentialNotNecessarilyReading
    (ActualParticularCauseCoevalWithEffect
      PotentialCauseAlwaysCoevalWithEffect : Prop) : Prop :=
  ActualParticularCauseCoevalWithEffect ∧
    ¬ PotentialCauseAlwaysCoevalWithEffect

/--
First premise of Aristotle's precision argument in *Physics* II.3, 195b21-25: if a human
builds, being a builder is the relevant explanation of that building.

Source: Aristotle, *Physics* II.3, 195b21-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def HumanBuildsQuaBuilderReading
    (HumanBuilds BuilderStatusExplainsBuilding : Prop) : Prop :=
  HumanBuilds → BuilderStatusExplainsBuilding

/--
Second premise of Aristotle's precision argument in *Physics* II.3, 195b21-25: the builder
builds in virtue of the building art, making that art the prior and more precise cause.

Source: Aristotle, *Physics* II.3, 195b21-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BuilderBuildsThroughBuildingArtReading
    (BuilderStatusExplainsBuilding BuildingArtIsMorePreciseCause : Prop) : Prop :=
  BuilderStatusExplainsBuilding → BuildingArtIsMorePreciseCause

/--
Conclusion of Aristotle's precision argument in *Physics* II.3, 195b21-25: when a human
builds, inquiry should reach the building art as the more precise cause.

Source: Aristotle, *Physics* II.3, 195b21-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BuildingArtMostPreciseCauseReading
    (HumanBuilds BuildingArtIsMorePreciseCause : Prop) : Prop :=
  HumanBuilds → BuildingArtIsMorePreciseCause

/--
Closing matching rule in Aristotle, *Physics* II.3, 195b25-30: generic effects are assigned
to generic causes and particular effects to particular causes; powers correspond to possible
effects and actually operating causes to effects being actualized.

Source: Aristotle, *Physics* II.3, 195b25-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MatchCauseEffectSpecificityAndActualityReading
    (GenericCausesMatchGenericEffects
      ParticularCausesMatchParticularEffects
      PowersMatchPossibleEffects
      ActualCausesMatchActualizedEffects : Prop) : Prop :=
  GenericCausesMatchGenericEffects ∧
    ParticularCausesMatchParticularEffects ∧
      PowersMatchPossibleEffects ∧
        ActualCausesMatchActualizedEffects

end TruthCore.Greek.Aristotle.Physics
