import TruthCore.Greek.Aristotle.Physics.BookI.Chapter6

namespace TruthCore.Greek.Aristotle.Physics

/--
Methodological opening of Aristotle, *Physics* I.7, 189b30-34: the account should first
consider what is common to every coming-to-be and only then the features peculiar to each
kind.

Source: Aristotle, *Physics* I.7, 189b30-34 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CommonGenerationBeforeParticularKindsReading
    (CommonAccountPrecedesParticularAccounts : Prop) : Prop :=
  CommonAccountPrecedesParticularAccounts

/--
Linguistic distinction in Aristotle, *Physics* I.7, 189b34-190a5: descriptions of becoming
may name simple terms, such as a man or the unmusical becoming musical, or compounds, such
as an unmusical man becoming a musical man.

The conjunction preserves both forms without treating grammatical simplicity as ontological
simplicity.

Source: Aristotle, *Physics* I.7, 189b34-190a5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SimpleAndCompositeBecomingDescriptionsReading
    (SimpleBecomingDescriptions CompositeBecomingDescriptions : Prop) : Prop :=
  SimpleBecomingDescriptions ∧ CompositeBecomingDescriptions

/--
Persistence distinction in Aristotle, *Physics* I.7, 190a5-13: in the example of becoming
musical, the human subject persists through the change, whereas the privative description
"unmusical" does not persist.

This remains scoped to the subject/opposite roles Aristotle is using to analyse change.

Source: Aristotle, *Physics* I.7, 190a5-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SubjectPersistsOppositeDoesNotReading
    (SubjectPersists OppositePersists : Prop) : Prop :=
  SubjectPersists ∧ ¬ OppositePersists

/--
Generalization in Aristotle, *Physics* I.7, 190a13-21: every case of becoming has an
underlying subject. That subject is numerically one, while its subject-description and its
privative description differ in account.

The formal conjunction does not identify numerical unity with identity in definition.

Source: Aristotle, *Physics* I.7, 190a13-21 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BecomingHasUnderlyingSubjectReading
    (EveryBecomingHasUnderlyingSubject SubjectNumericallyOne SubjectOneInAccount : Prop) : Prop :=
  EveryBecomingHasUnderlyingSubject ∧ SubjectNumericallyOne ∧ ¬ SubjectOneInAccount

/--
Category distinction in Aristotle, *Physics* I.7, 190a31-190b5: only substances come to be
without qualification; changes in quantity, quality, relation, time, or place are qualified
becomings that presuppose a subject.

Source: Aristotle, *Physics* I.7, 190a31-190b5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def UnqualifiedAndQualifiedBecomingReading
    (OnlySubstancesComeToBeUnqualified QualifiedBecomingPresupposesSubject : Prop) : Prop :=
  OnlySubstancesComeToBeUnqualified ∧ QualifiedBecomingPresupposesSubject

/--
Extension to substance in Aristotle, *Physics* I.7, 190b5-10: substances and other things
that come to be without qualification also arise from an underlying subject, as plants and
animals arise from seed.

This states the source's substratum claim without asserting that every seed remains unchanged
in the resulting organism.

Source: Aristotle, *Physics* I.7, 190b5-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SubstancesComeToBeFromUnderlyingSubjectReading
    (SubstancesComeToBeFromUnderlyingSubject : Prop) : Prop :=
  SubstancesComeToBeFromUnderlyingSubject

/--
Survey of generative modes in Aristotle, *Physics* I.7, 190b10-17: shaping, addition,
subtraction, composition, and alteration all produce what comes to be from an underlying
subject.

The five modes are retained together because they support one shared substratum conclusion;
the examples are not inflated into five independent philosophical claims.

Source: Aristotle, *Physics* I.7, 190b10-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GenerativeModesProceedFromSubjectsReading
    (ShapingFromSubject AdditionFromSubject SubtractionFromSubject
      CompositionFromSubject AlterationFromSubject : Prop) : Prop :=
  ShapingFromSubject ∧ AdditionFromSubject ∧ SubtractionFromSubject ∧
    CompositionFromSubject ∧ AlterationFromSubject

/--
Composite analysis in Aristotle, *Physics* I.7, 190b17-23: everything that comes to be has
both something that becomes and something it becomes; the source term can be analysed as the
underlying subject or as the opposed condition.

Source: Aristotle, *Physics* I.7, 190b17-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EveryBecomingCompositeReading
    (HasSomethingThatBecomes HasOutcome SourceIsSubjectOrOpposite : Prop) : Prop :=
  HasSomethingThatBecomes ∧ HasOutcome ∧ SourceIsSubjectOrOpposite

/--
Conditional principles claim in Aristotle, *Physics* I.7, 190b23-29: if natural things have
first non-incidental causes and principles from which they come to be, then each comes to be
from an underlying subject and a form.

The antecedent is retained rather than promoted to a new premise solely to make a proof pass.

Source: Aristotle, *Physics* I.7, 190b23-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalGenerationFromSubjectAndFormReading
    (NaturalThingsHaveFirstPrinciples GenerationFromSubjectAndForm : Prop) : Prop :=
  NaturalThingsHaveFirstPrinciples → GenerationFromSubjectAndForm

/--
Matter/privation distinction in Aristotle, *Physics* I.7, 190b29-34: the underlying matter
is the non-incidental subject from which the result comes to be, whereas privation and
contrariety belong incidentally to that subject.

Source: Aristotle, *Physics* I.7, 190b29-34 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MatterSubjectPrivationIncidentalReading
    (MatterIsNonIncidentalSubject PrivationIsIncidentalToSubject : Prop) : Prop :=
  MatterIsNonIncidentalSubject ∧ PrivationIsIncidentalToSubject

/--
Qualified count in Aristotle, *Physics* I.7, 190b29-191a7: the principles can be called two
in one respect and three in another because subject, privation, and form differ in being even
where one subject is numerically involved.

This does not identify the qualified two with a simple subset of the three or erase the
chapter's distinctions of account.

Source: Aristotle, *Physics* I.7, 190b29-191a7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PrinciplesTwoInOneSenseThreeInAnotherReading
    (PrinciplesTwoInOneSense PrinciplesThreeInAnotherSense : Prop) : Prop :=
  PrinciplesTwoInOneSense ∧ PrinciplesThreeInAnotherSense

/--
Resolution in Aristotle, *Physics* I.7, 190b35-191a3: although contraries cannot act on one
another, the underlying subject is distinct from them and is not itself a contrary, removing
that obstacle to the account of change.

Source: Aristotle, *Physics* I.7, 190b35-191a3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DistinctNonContrarySubjectResolvesOppositionReading
    (ContrariesCannotAffectEachOther SubjectDistinctFromContraries SubjectIsContrary
      OppositionObstacleResolved : Prop) : Prop :=
  ContrariesCannotAffectEachOther ∧ SubjectDistinctFromContraries ∧ ¬ SubjectIsContrary →
    OppositionObstacleResolved

/--
Epistemic account in Aristotle, *Physics* I.7, 191a7-12: the underlying nature is known by
analogy, as bronze stands to a statue or wood to a bed before receiving form.

The analogy establishes an explanatory relation; it does not assert literal identity among
the materials in the examples.

Source: Aristotle, *Physics* I.7, 191a7-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def UnderlyingNatureKnownByAnalogyReading
    (UnderlyingNatureKnownAnalogically : Prop) : Prop :=
  UnderlyingNatureKnownAnalogically

/--
Closing synthesis in Aristotle, *Physics* I.7, 191a12-22: subject, form, and privation are
the three principles in the qualified sense now explained. Aristotle nevertheless leaves
unresolved whether form or the underlying subject is the substance of a natural thing.

Source: Aristotle, *Physics* I.7, 191a12-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ThreePrinciplesSubstanceQuestionOpenReading
    (SubjectIsPrinciple FormIsPrinciple PrivationIsPrinciple
      FormOrSubjectAsSubstanceResolved : Prop) : Prop :=
  SubjectIsPrinciple ∧ FormIsPrinciple ∧ PrivationIsPrinciple ∧
    ¬ FormOrSubjectAsSubstanceResolved

end TruthCore.Greek.Aristotle.Physics
