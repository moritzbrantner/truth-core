import TruthCore.Greek.Aristotle.Physics.BookII.Chapter4

namespace TruthCore.Greek.Aristotle.Physics

/--
Domain restriction in Aristotle, *Physics* II.5, 196b10-17: chance is not said to cause what
happens necessarily and always or what happens for the most part. Chance events instead occur
outside those regular domains, and their acknowledged occurrence establishes that chance and
spontaneity are not nothing.

Source: Aristotle, *Physics* II.5, 196b10-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChanceAppliesToExceptionalEventsReading
    (ChanceCausesNecessaryOrAlways ChanceCausesUsual
      ChanceEventsOccurOutsideNecessaryAndUsual ChanceAndSpontaneityExist : Prop) : Prop :=
  ¬ ChanceCausesNecessaryOrAlways ∧
    ¬ ChanceCausesUsual ∧
      ChanceEventsOccurOutsideNecessaryAndUsual ∧
        ChanceAndSpontaneityExist

/--
Purposive-domain classification in Aristotle, *Physics* II.5, 196b17-23: some things happen
for an end and others do not; among the former, some involve choice and some do not, while
both deliberate action and natural generation can be for an end. Exceptional events can
therefore still fall within the purposive domain.

Source: Aristotle, *Physics* II.5, 196b17-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PurposiveDomainIncludesChoiceAndNatureReading
    (SomeEventsAreForEnds
      PurposiveEventsCanInvolveChoice
      PurposiveEventsCanLackChoice
      DeliberateActionsAreForEnds
      NaturalProcessesAreForEnds
      ExceptionalEventsCanBePurposive : Prop) : Prop :=
  SomeEventsAreForEnds ∧
    PurposiveEventsCanInvolveChoice ∧
      PurposiveEventsCanLackChoice ∧
        DeliberateActionsAreForEnds ∧
          NaturalProcessesAreForEnds ∧
            ExceptionalEventsCanBePurposive

/--
Causal distinction in Aristotle, *Physics* II.5, 196b23-29: the craft of building is a
proper cause of a house, while a coincident attribute such as being pale or musical is an
incidental cause; the proper cause is definite, whereas incidental causes are indefinite
because indefinitely many attributes can coincide in one thing.

This extends rather than re-identifies the II.3 taxonomy of incidental causes.

Source: Aristotle, *Physics* II.5, 196b23-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ProperCauseDefiniteIncidentalCauseIndefiniteReading
    (BuildingCraftProperlyCausesHouse
      CoincidentAttributesIncidentallyCauseHouse
      ProperCauseIsDefinite
      IncidentalCausesAreIndefinite : Prop) : Prop :=
  BuildingCraftProperlyCausesHouse ∧
    CoincidentAttributesIncidentallyCauseHouse ∧
      ProperCauseIsDefinite ∧
        IncidentalCausesAreIndefinite

/--
Inferential condition developed in Aristotle, *Physics* II.5, 196b29-197a8: when an outcome
could be chosen for an end, is not brought about for that end, occurs incidentally, and is
neither necessary nor usual, it occurs by chance.

The choice qualification distinguishes chance within the broader purposive domain; it does
not yet collapse chance into spontaneity, whose difference is treated in II.6.

Source: Aristotle, *Physics* II.5, 196b29-197a8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ExceptionalIncidentalChosenEndImpliesChanceReading
    (OutcomeCouldBeChosenForEnd OutcomeWasBroughtAboutForThatEnd
      OutcomeOccursIncidentally OutcomeIsNecessaryOrUsual
      OutcomeOccursByChance : Prop) : Prop :=
  OutcomeCouldBeChosenForEnd ∧
      ¬ OutcomeWasBroughtAboutForThatEnd ∧
        OutcomeOccursIncidentally ∧
          ¬ OutcomeIsNecessaryOrUsual →
    OutcomeOccursByChance

/--
Premises of Aristotle's marketplace example in *Physics* II.5, 196b33-197a5: recovering a
contribution could have been a chosen end, but the visitor did not come for repayment; the
visit was neither necessary nor usual, and repayment occurred incidentally upon the visit.

Source: Aristotle, *Physics* II.5, 196b33-197a5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MarketplaceRepaymentChanceConditionsReading
    (RepaymentCouldBeChosenEnd VisitorCameForRepayment
      VisitWasNecessaryOrUsual RepaymentOccurredIncidentally : Prop) : Prop :=
  RepaymentCouldBeChosenEnd ∧
    ¬ VisitorCameForRepayment ∧
      ¬ VisitWasNecessaryOrUsual ∧
        RepaymentOccurredIncidentally

/--
Conclusion of Aristotle's marketplace example in *Physics* II.5, 197a1-5: under the stated
conditions, the visitor's recovery of the contribution occurs by chance.

Source: Aristotle, *Physics* II.5, 197a1-5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MarketplaceRepaymentByChanceReading
    (RepaymentOccurredByChance : Prop) : Prop :=
  RepaymentOccurredByChance

/--
Central definition in Aristotle, *Physics* II.5, 197a5-8: chance is an incidental cause among
events that are for an end and according to choice. Thought and chance concern the same
domain because choice is not without thought.

Source: Aristotle, *Physics* II.5, 197a5-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChanceIncidentalCauseInChosenEndsReading
    (ChanceIsIncidentalCause
      ChanceOccursAmongChosenPurposiveEvents
      ChoiceRequiresThought
      ThoughtAndChanceConcernSameDomain : Prop) : Prop :=
  ChanceIsIncidentalCause ∧
    ChanceOccursAmongChosenPurposiveEvents ∧
      ChoiceRequiresThought ∧
        ThoughtAndChanceConcernSameDomain

/--
Qualified causal status in Aristotle, *Physics* II.5, 197a8-21: because the incidental
causes from which chance events arise are indefinite, chance is indefinite and obscure to
human beings. Chance is a cause incidentally, but not a cause of anything without
qualification.

Source: Aristotle, *Physics* II.5, 197a8-21 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChanceIndefiniteAndQualifiedCauseReading
    (ChanceCausesAreIndefinite
      ChanceIsIndefinite
      ChanceIsObscureToHumans
      ChanceIsIncidentalCause
      ChanceIsCauseWithoutQualification : Prop) : Prop :=
  ChanceCausesAreIndefinite ∧
    ChanceIsIndefinite ∧
      ChanceIsObscureToHumans ∧
        ChanceIsIncidentalCause ∧
          ¬ ChanceIsCauseWithoutQualification

/--
Explanation of a common description in Aristotle, *Physics* II.5, 197a21-25: rational
accounts concern what is always so or so for the most part, whereas chance belongs among
exceptions to those domains; in that qualified sense chance is said to be contrary to reason.

Source: Aristotle, *Physics* II.5, 197a21-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChanceContraryToReasonExplainedReading
    (RationalAccountsConcernAlwaysOrUsual
      ChanceConcernsExceptionsToAlwaysOrUsual
      ChanceIsContraryToReasonInThisSense : Prop) : Prop :=
  RationalAccountsConcernAlwaysOrUsual ∧
    ChanceConcernsExceptionsToAlwaysOrUsual ∧
      ChanceIsContraryToReasonInThisSense

/--
Fortune and summary in Aristotle, *Physics* II.5, 197a25-37: outcomes determine good or bad
fortune, large outcomes determine success or misfortune, and fortune is unstable because
chance events are neither always nor usual. Chance and spontaneity are both incidental
causes among exceptional events capable of occurring for an end.

This final summary preserves the common scope of chance and spontaneity without anticipating
their II.6 difference.

Source: Aristotle, *Physics* II.5, 197a25-37 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FortuneValenceMagnitudeInstabilitySummaryReading
    (GoodOutcomeMakesGoodFortune
      BadOutcomeMakesBadFortune
      GreatOutcomeMakesSuccessOrMisfortune
      FortuneIsUnstable
      ChanceAndSpontaneityAreIncidentalCauses
      TheirEventsAreExceptionalAndPurposive : Prop) : Prop :=
  GoodOutcomeMakesGoodFortune ∧
    BadOutcomeMakesBadFortune ∧
      GreatOutcomeMakesSuccessOrMisfortune ∧
        FortuneIsUnstable ∧
          ChanceAndSpontaneityAreIncidentalCauses ∧
            TheirEventsAreExceptionalAndPurposive

end TruthCore.Greek.Aristotle.Physics
