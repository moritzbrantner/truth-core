import TruthCore.Greek.Aristotle.Physics

namespace TruthCore.Greek.Aristotle.Physics

/--
Methodological reading of Aristotle, *Physics* I.1, 184a10-16: when a subject matter has
principles, causes, or elements, scientific knowledge of it requires acquaintance with its
primary causes and principles and analysis down to its elements.

This is a methodological condition on knowledge in the relevant sciences, not a claim that
all knowledge whatsoever has the same structure.

Source: Aristotle, *Physics* I.1, 184a10-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ScientificKnowledgeThroughFirstPrinciplesReading
    (ScientificKnowledgeOfSubject : Prop)
    (KnowsPrimaryPrinciplesCausesElements : Prop) : Prop :=
  ScientificKnowledgeOfSubject → KnowsPrimaryPrinciplesCausesElements

/--
Immediate application in Aristotle, *Physics* I.1, 184a14-16: natural science should begin
by determining what concerns its principles.

Source: Aristotle, *Physics* I.1, 184a14-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalScienceBeginsWithPrinciplesReading
    (NaturalScienceInquiry : Prop)
    (DeterminePrinciplesFirst : Prop) : Prop :=
  NaturalScienceInquiry → DeterminePrinciplesFirst

/--
Epistemic-order reading of Aristotle, *Physics* I.1, 184a16-21: inquiry proceeds from what is
more evident and knowable to us toward what is clearer and more knowable by nature, since the
two orders of knowability are not identical.

The predicates are left primitive rather than identified with a modern psychological or
logical notion of evidence.

Source: Aristotle, *Physics* I.1, 184a16-21 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InquiryFromKnowableToUsToKnowableByNatureReading
    (BeginsFromKnowableToUs : Prop)
    (ProceedsTowardKnowableByNature : Prop)
    (OrdersAreIdentical : Prop) : Prop :=
  BeginsFromKnowableToUs ∧
    ProceedsTowardKnowableByNature ∧
    ¬ OrdersAreIdentical

/--
Analytic-progression reading of Aristotle, *Physics* I.1, 184a21-184b14: what is initially
clear to us is a comparatively undifferentiated whole; by division or analysis its elements,
principles, and more determinate parts become known.

The examples of names and children's broad classifications illustrate this structure and are
not promoted to separate philosophical theses.

Source: Aristotle, *Physics* I.1, 184a21-184b14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AnalysisFromConfusedWholeToPrinciplesReading
    (InitiallyKnownAsConfusedWhole : Prop)
    (AnalysisDisclosesPrinciplesAndParts : Prop) : Prop :=
  InitiallyKnownAsConfusedWhole ∧ AnalysisDisclosesPrinciplesAndParts

end TruthCore.Greek.Aristotle.Physics
