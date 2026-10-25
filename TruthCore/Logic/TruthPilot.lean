/-!
The objective-truth pilot (#207) separates proofs in Lean's logic from readings
about truth, endorsement and knowledge. Its profile semantics is stipulated for
countermodels; no identification with Aristotle's or a modern relativist's
semantics is assumed. Aristotle, Metaphysics IV.5, distinguishes all appearances
being true, conflicting opinions, and the fork 'nothing true / unknown to us'.
Those readings have separate corpus identities.
-/
namespace TruthCore.Logic.TruthPilot

/-- A proposition has a proof in the encoded logic, not a mind-independence thesis. -/
def SomePropositionHolds : Prop := ∃ P : Prop, P

/-- It is not the case that every proposition fails, within the encoded logic. -/
def NotEveryPropositionFails : Prop := ¬ (∀ P : Prop, ¬ P)

/-- Test sentences include a logical sentence and a taste sentence. This is a
small stipulated language, not a classification of every natural-language claim. -/
inductive Sentence where
  | logical
  | taste
  deriving DecidableEq

/-- Two agents suffice to distinguish disagreement from truth variation. -/
inductive Agent where
  | first
  | second
  deriving DecidableEq

/-- A possible distribution of endorsements; endorsement is not truth. -/
abbrev Profile := Agent → Sentence → Prop

/-- An interpretation assigns a proposition to each sentence under each profile. -/
abbrev Interpretation := Profile → Sentence → Prop

/-- All sentences change truth under some change of endorsement profile. A strong
stipulated global reading; not attributed to Protagoras from Aristotle's report. -/
def GlobalProfileVariation (Holds : Interpretation) : Prop :=
  ∀ s, ∃ E F, Holds E s ∧ ¬ Holds F s

/-- Some sentence changes truth under endorsement profiles, without the global scope. -/
def LocalProfileVariation (Holds : Interpretation) : Prop :=
  ∃ s E F, Holds E s ∧ ¬ Holds F s

/-- A stronger-than-minimal philosophical bridge: this interpretation preserves a
logical sentence as true under every profile. A Lean proof of SomePropositionHolds
alone supplies no interpretation, sentence translation, or profile invariance. -/
def LogicalSentenceStable (Holds : Interpretation) : Prop :=
  ∀ E, Holds E Sentence.logical

/-- The strong global profile thesis fails, relative to the supplied interpretation. -/
def NotGlobalProfileVariation (Holds : Interpretation) : Prop :=
  ¬ GlobalProfileVariation Holds

/-- Disagreement is endorsement of a sentence and withholding its endorsement
by another agent. Withholding here is not endorsement of its negation. -/
def Disagreement (E : Profile) : Prop :=
  ∃ s, E Agent.first s ∧ ¬ E Agent.second s

/-- Limited knowledge: an agent does not know every sentence. No denial of truth
or endorsement-relative truth follows just from this epistemic condition. -/
def LimitedKnowledge (Knows : Agent → Sentence → Prop) : Prop :=
  ∃ a s, ¬ Knows a s

/-- A profile interpretation can keep the logical sentence true under every
endorsement profile while the taste sentence changes truth between profiles. -/
def LogicalTruthsCompatibleWithVariation : Prop :=
  ∃ Holds : Interpretation, LogicalSentenceStable Holds ∧ LocalProfileVariation Holds

/-- A global variation model when the stability bridge is absent. Its consistency
is consistency of this small encoding, not a defense of a complete worldview. -/
def GlobalVariationModelExists : Prop :=
  ∃ Holds : Interpretation, GlobalProfileVariation Holds

/-- Disagreement and limited knowledge coexist with profile-invariant truths. -/
def EpistemicDifferencesDoNotRequireRelativity : Prop :=
  ∃ (Holds : Interpretation) (E : Profile) (Knows : Agent → Sentence → Prop),
    Disagreement E ∧ LimitedKnowledge Knows ∧
      (∀ F G s, Holds F s ↔ Holds G s)

/-- A source-reading schema, Aristotle Metaphysics IV.5, 1009a6-15: whatever an
agent opines is true without relativizing the truth predicate to that agent. The
passage is Aristotle's report of the Protagorean target, not direct Protagoras. -/
def AllOpinionsTrue {Person Content : Type}
    (Opines : Person → Content → Prop) (TrueAtIssue : Content → Prop) : Prop :=
  ∀ a p, Opines a p → TrueAtIssue p

/-- Conflicting opinions at one content and its expressed negation. The mapping
from expressed negation to logical negation must be supplied separately. -/
def ConflictingOpinions {Person Content : Type}
    (Opines : Person → Content → Prop) (neg : Content → Content) : Prop :=
  ∃ a b p, Opines a p ∧ Opines b (neg p)

/-- A weaker sibling reading of IV.5, 1009a9-12: different people hold
opposed opinions. The source word for opposites need not itself mean logical
negation; no contradiction follows without an interpretation of Opposes. -/
def OpposedOpinions {Person Content : Type}
    (Opines : Person → Content → Prop) (Opposes : Content → Content → Prop) : Prop :=
  ∃ a b p q, Opines a p ∧ Opines b q ∧ Opposes p q

/-- The explicit logical-negation bridge for the test of Aristotle's target.
Without it the target's truth predicate could be paraconsistent or indexed. -/
def NegationRespected {Content : Type}
    (TrueAtIssue : Content → Prop) (neg : Content → Content) : Prop :=
  ∀ p, TrueAtIssue (neg p) → ¬ TrueAtIssue p

/-- The all-opinions-true schema fails under the supplied opinion/truth interpretation. -/
def NotAllOpinionsTrue {Person Content : Type}
    (Opines : Person → Content → Prop) (TrueAtIssue : Content → Prop) : Prop :=
  ¬ AllOpinionsTrue Opines TrueAtIssue

end TruthCore.Logic.TruthPilot
