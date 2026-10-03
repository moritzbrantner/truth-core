import TruthCore.Greek.Aristotle.Physics.BookII.Chapter6

namespace TruthCore.Greek.Aristotle.Physics

/--
Inferential bridge in Aristotle, *Physics* II.7, 198a14-24: if the four causal modes exhaust
the ultimate answers to “why,” then the physicist must know all four and refer physical
questions to matter, form, source of motion, and end.

Source: Aristotle, *Physics* II.7, 198a14-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FourCauseExhaustivenessImpliesPhysicalScopeReading
    (FourCausesExhaustWhy PhysicistMustKnowAllFourCauses : Prop) : Prop :=
  FourCausesExhaustWhy → PhysicistMustKnowAllFourCauses

/--
Methodological conclusion in Aristotle, *Physics* II.7, 198a22-24: the physicist must know
all four causes and answer the why physically by reference to matter, form, mover, and end.

Source: Aristotle, *Physics* II.7, 198a22-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PhysicistKnowsAllFourCausesReading
    (PhysicistMustKnowAllFourCauses : Prop) : Prop :=
  PhysicistMustKnowAllFourCauses

/--
Convergence qualification in Aristotle, *Physics* II.7, 198a24-27: form or essence, end,
and primary mover often converge. Essence and end are one in such cases, while the primary
mover is the same in species, as a human generates a human.

The qualification “often” is preserved; the three modes are not globally identified.

Source: Aristotle, *Physics* II.7, 198a24-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FormEndMoverOftenConvergeReading
    (FormAndEndOftenCoincide
      PrimaryMoverOftenSameInSpeciesAsFormAndEnd
      HumanGeneratesHuman : Prop) : Prop :=
  FormAndEndOftenCoincide ∧
    PrimaryMoverOftenSameInSpeciesAsFormAndEnd ∧
      HumanGeneratesHuman

/--
Disciplinary boundary in Aristotle, *Physics* II.7, 198a27-31: things that move while being
moved fall within physics, whereas unmoved movers do not move through an internal source of
motion and lie outside it. Aristotle consequently distinguishes inquiries into unmoved
things, moving imperishable things, and perishable things.

Source: Aristotle, *Physics* II.7, 198a27-31 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MovedMoversAndThreeInquiryDomainsReading
    (MovedMoversBelongToPhysics
      UnmovedMoversBelongToPhysics
      UnmovedMoversHaveInternalMotionSource
      InquiryIntoUnmovedThings
      InquiryIntoMovingImperishableThings
      InquiryIntoPerishableThings : Prop) : Prop :=
  MovedMoversBelongToPhysics ∧
    ¬ UnmovedMoversBelongToPhysics ∧
      ¬ UnmovedMoversHaveInternalMotionSource ∧
        InquiryIntoUnmovedThings ∧
          InquiryIntoMovingImperishableThings ∧
            InquiryIntoPerishableThings

/--
Method for generation in Aristotle, *Physics* II.7, 198a31-35: explanation refers to matter,
essence, and primary mover; investigation especially follows what comes after what and traces
the first agent or patient and each subsequent stage.

Source: Aristotle, *Physics* II.7, 198a31-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GenerationExplanationTracesCausalSequenceReading
    (GenerationWhyRefersToMatterEssencePrimaryMover
      InvestigationTracksWhatFollowsWhat
      InvestigationTracksFirstAgentOrPatient
      InvestigationContinuesThroughSuccessiveStages : Prop) : Prop :=
  GenerationWhyRefersToMatterEssencePrimaryMover ∧
    InvestigationTracksWhatFollowsWhat ∧
      InvestigationTracksFirstAgentOrPatient ∧
        InvestigationContinuesThroughSuccessiveStages

/--
Moving-principle distinction in Aristotle, *Physics* II.7, 198a35-198b4: two principles are
relevant to physical motion, though one is not itself physical because it lacks an internal
source of motion. Aristotle associates this side with the wholly unmoved first principle and
with essence or form as end.

This records the chapter's boundary without identifying every mentioned item as numerically
one or importing a later unmoved-mover proof.

Source: Aristotle, *Physics* II.7, 198a35-198b4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MovingPrinciplePhysicalBoundaryReading
    (TwoMovingPrinciplesRelevantToPhysics
      OneMovingPrincipleIsNotPhysical
      NonPhysicalPrincipleLacksInternalMotionSource
      WhollyUnmovedFirstPrincipleIsSuch
      EssenceAndFormServeAsEnd : Prop) : Prop :=
  TwoMovingPrinciplesRelevantToPhysics ∧
    OneMovingPrincipleIsNotPhysical ∧
      NonPhysicalPrincipleLacksInternalMotionSource ∧
        WhollyUnmovedFirstPrincipleIsSuch ∧
          EssenceAndFormServeAsEnd

/--
Final-cause obligation in Aristotle, *Physics* II.7, 198b3-5: because nature is for an end,
the physicist must also know the form or final cause.

Source: Aristotle, *Physics* II.7, 198b3-5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalTeleologyRequiresFinalCauseKnowledgeReading
    (NatureActsForEnds PhysicistMustKnowFinalCause : Prop) : Prop :=
  NatureActsForEnds → PhysicistMustKnowFinalCause

/--
Closing explanatory inventory in Aristotle, *Physics* II.7, 198b5-9: the physicist must say
how one thing follows necessarily or usually from another, what must be so if an outcome is
to be, what the essence is, and why the arrangement is better relative to that thing's own
essence rather than better without qualification.

Source: Aristotle, *Physics* II.7, 198b5-9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PhysicalExplanationCompleteWhyInventoryReading
    (ExplainNecessaryOrUsualMaterialConsequence
      ExplainHypotheticalNecessityForOutcome
      ExplainEssence
      ExplainBetterRelativeToOwnEssence
      ExplainBetterWithoutQualification : Prop) : Prop :=
  ExplainNecessaryOrUsualMaterialConsequence ∧
    ExplainHypotheticalNecessityForOutcome ∧
      ExplainEssence ∧
        ExplainBetterRelativeToOwnEssence ∧
          ¬ ExplainBetterWithoutQualification

end TruthCore.Greek.Aristotle.Physics
