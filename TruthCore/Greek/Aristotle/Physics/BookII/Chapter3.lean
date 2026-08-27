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

end TruthCore.Greek.Aristotle.Physics
