module

public import TruthCore.Alternatives.MindPhysicalism

/-!
Intentionality investigation #943, explicit analyst configurations under the
owner’s logic-first direction (2026-11-05). Historical comparison is deferred;
consulted findings and precise locators are in docs/notes/intentionality-943.md.
No author is attributed these formal universals. The self-affection restriction
and a relational consumer-function alternative are tested on the same tokens.

`MindPhysicalism.Frame` continues to own occurrence identity, kind membership,
physicality and causation. Its target kind is instantiated here as categorical
judgments/signals, not silently identified with every q.75 intellectual exercise.
The new structure adds content evaluation, which that frame lacks. FormReception
(q.14) concerns aptitude for forms, not truth-evaluable judgments; q.75's
CanUnderstand concerns bodily natures, not correctness. No replacement of either.
-/

@[expose] public section
namespace TruthCore.Alternatives.Intentionality943

open TruthCore.Alternatives.MindPhysicalism

/-- A categorical token has a content evaluated at situations, and can occur
without that content obtaining. `Report e w` evaluates a proposed report about
the token’s own affection; it is distinct from both occurrence and content.
There is no accessibility relation, modal necessity, subject/property identity,
or presumption of veridicality. Empty carriers are permitted by the interface;
the error premise supplies both a token and a situation. -/
structure Semantics (Occurrence Content Situation : Type) where
  content : Occurrence → Content
  Holds : Content → Situation → Prop
  Occurs : Occurrence → Situation → Prop
  Report : Occurrence → Situation → Prop

/-- At least one occurrence of the target mental kind has false content at
its situation. This is an explicit framework input, not an empirical theorem
or an assertion that Papineau's hypothetical monkeys actually behave thus. -/
def SomeError {Occurrence Kind Content Situation : Type}
    (f : Frame Occurrence Kind) (s : Semantics Occurrence Content Situation) : Prop :=
  ∃ e w, f.Mental e ∧ s.Occurs e w ∧ ¬ s.Holds (s.content e) w

/-- Restricted self-report: at each situation where a target token occurs,
the report of its affection *as it is affected* is true. This qualified ideal
report is not arbitrary introspection, and says nothing of absent tokens.
An analyst stipulation; historical comparison at ST I q.85 a.2 co. [32026]
is deferred, as documented in the linked note. -/
def AffectionReportCorrect {Occurrence Kind Content Situation : Type}
    (f : Frame Occurrence Kind) (s : Semantics Occurrence Content Situation) : Prop :=
  ∀ e w, f.Mental e → s.Occurs e w → s.Report e w

/-- The rejected restriction: content truth is just truth of the report about
the token’s own affection. This is truth-condition equivalence, NOT identity
of mental and physical occurrences. A physicalist can reject this restriction.
Comparison with q.85 a.2 co. [32026] and ad 3 [32029] is deferred.
No identification of initial form reception with categorical judgment is used. -/
def ContentOnlyAffectionReport {Occurrence Kind Content Situation : Type}
    (f : Frame Occurrence Kind) (s : Semantics Occurrence Content Situation) : Prop :=
  ∀ e w, f.Mental e → (s.Holds (s.content e) w ↔ s.Report e w)

/-- Every occurring target token has true content at its situation. It need
not be true at other situations. This is the unacceptable consequence isolated
by this analyst investigation, not a thesis attributed to physicalists generally. -/
def EveryOccurrenceAccurate {Occurrence Kind Content Situation : Type}
    (f : Frame Occurrence Kind) (s : Semantics Occurrence Content Situation) : Prop :=
  ∀ e w, f.Mental e → s.Occurs e w → s.Holds (s.content e) w

/-- The consequence of the error constraint: this particular identification
of content truth with affection-report truth must be rejected. It does not
exclude a physical token bearing an externally directed content. -/
def RejectContentOnlyAffection {Occurrence Kind Content Situation : Type}
    (f : Frame Occurrence Kind) (s : Semantics Occurrence Content Situation) : Prop :=
  ¬ ContentOnlyAffectionReport f s

/-- A minimal analyst interface for a producer/consumer configuration.
Deferred comparison: Papineau, Teleosemantics, pp.97–100,111. Here, SelectedFor e b g means the token-producing arrangement has an etiological
function of enabling response b toward end g. SuccessCondition b g w is the
condition under which b would serve that specific end under proper functioning,
not whichever outcome happens to be lucky on an occasion (pp.102–104).
No causal, transitivity, asymmetry or well-foundedness law is assumed here.
This interface does not independently naturalize either primitive relation. -/
structure Consumer (Occurrence Response End Situation : Type) where
  SelectedFor : Occurrence → Response → End → Prop
  SuccessCondition : Response → End → Situation → Prop

/-- Stipulated consumer-function configuration: each target representation is
associated with an etiological producer/consumer function, and its truth
condition is the condition for the consumer response to serve the specific
end. The existence clause prevents an empty selection relation from making
the reading vacuous on an existing target token. No actual success is required. -/
def ConsumerContent {Occurrence Kind Content Situation Response End : Type}
    (f : Frame Occurrence Kind) (s : Semantics Occurrence Content Situation)
    (c : Consumer Occurrence Response End Situation) : Prop :=
  ∀ e, f.Mental e → ∃ b g, c.SelectedFor e b g ∧
    ∀ w, s.Holds (s.content e) w ↔ c.SuccessCondition b g w

/-- Existence of one joint finite-profile interpretation with the causal
background, reductive target-kind classification, consumer content, an accurate
affection report and an erroneous target token. Existentially quantifying the
carriers does not assert that all such interpretations are finite or realized
in nature. The Solution supplies finite carriers. -/
def PhysicalistErrorModelExists : Prop :=
  ∃ (Occurrence Kind Content Situation Response End : Type)
    (f : Frame Occurrence Kind) (s : Semantics Occurrence Content Situation)
    (c : Consumer Occurrence Response End Situation),
    CausalBackground f ∧ Reductive f ∧ ConsumerContent f s c ∧
    AffectionReportCorrect f s ∧ SomeError f s ∧ RejectContentOnlyAffection f s

end TruthCore.Alternatives.Intentionality943
