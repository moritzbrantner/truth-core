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

end TruthCore.Greek.Aristotle.Physics
