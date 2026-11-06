module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.UpperLower.Closure
public import TruthCore.Logic.KnowabilityCompatibility

/-!
Analyst semantic model for #1065; attribution deferred. Information grows along
the three-stage order, independently of epistemic and modal accessibility.
Contents are ALL persistent upper sets with Mathlib's genuine Heyting operations.
`UpperSet` is reverse-inclusion ordered, hence its order dual is used for truth.

The old Frame/relational knowledge/possible-knowledge operators are reused where
their meanings coincide. The old pointwise `FitchKnowability.Moore` is NOT used:
intuitionistic negation quantifies over information extensions. Metalanguage
non-forcing is likewise not object-language negation. No whole modal calculus,
physical time, human competence or truth of an antirealist worldview is asserted.
-/

@[expose] public section

namespace TruthCore.Logic.IntuitionisticKnowability

open OrderDual
open TruthCore.Modal TruthCore.Logic

abbrev World := Fin 3

/-- Persistent truth contents, ordered by inclusion. -/
abbrev Content := (UpperSet World)ᵒᵈ

def holds (p : Content) (w : World) : Prop := w ∈ ofDual p

/-- Reuse the first three worlds of the earlier four-world epistemic model. -/
def includeWorld (w : World) : Fin 4 := ⟨w.val, lt_trans w.isLt (by decide)⟩

def epistemic : TruthCore.Modal.Frame World where
  access u v := FitchKnowability.survivorEpistemic.access (includeWorld u) (includeWorld v)

def modal : TruthCore.Modal.Frame World where
  access u v := KnowabilityCompatibility.universalModal.access (includeWorld u) (includeWorld v)

def actual : World := 1

/-- Only matching relational operators are shared with the earlier Context. -/
def relational : FitchKnowability.Context World :=
  KnowabilityCompatibility.relationalContext epistemic modal actual

/-- Upper closure is a type-safe constructor. OperatorsExact proves that it
adds NO world to raw relational knowledge on this model's persistent contents. -/
def knows (p : Content) : Content :=
  toDual (upperClosure {w | relational.knows (holds p) w})

/-- The corresponding persistent possibility operator; its raw relation is
universal and its exact relational interpretation is separately checked. -/
def possible (p : Content) : Content :=
  toDual (upperClosure {w | ∃ v, modal.access w v ∧ holds p v})

/-- This is Heyting pseudocomplement, not pointwise Boolean complement. -/
def moore (p : Content) : Content := p ⊓ (knows p)ᶜ

/-- The selected content first becomes true at the middle information stage. -/
def atom : Content := toDual (UpperSet.Ici (1 : World))

def FutureForcing : Prop :=
  (∀ (p q : Content) w,
    holds (p ⇨ q) w ↔ ∀ v, w ≤ v → holds p v → holds q v) ∧
  (∀ (p : Content) w,
    holds pᶜ w ↔ ∀ v, w ≤ v → ¬ holds p v)

def OperatorsExact : Prop :=
  (∀ (p : Content) w,
    holds (knows p) w ↔ JustificationIntrospection.Knows epistemic (holds p) w) ∧
  (∀ (p : Content) w,
    holds (possible p) w ↔ ∃ v, modal.access w v ∧ holds p v) ∧
  (∀ (p : Content) w,
    holds (possible (knows p)) w ↔ FitchKnowability.PossibleKnown relational (holds p) w)

def FrameProfile : Prop :=
  TruthCore.Modal.Reflexive epistemic ∧ TruthCore.Modal.Symmetric epistemic ∧
    TruthCore.Modal.Transitive epistemic ∧
    TruthCore.Modal.Reflexive modal ∧ TruthCore.Modal.Symmetric modal ∧
    TruthCore.Modal.Transitive modal ∧
    KnowabilityCompatibility.Included epistemic modal

/-- These are the advertised individual laws, not the name of an entire
constructive modal calculus. Negative introspection uses Heyting negation. -/
def EpistemicLaws : Prop :=
  knows ⊤ = ⊤ ∧
  (∀ p q, knows (p ⊓ q) = knows p ⊓ knows q) ∧
  (∀ p, knows p ≤ p) ∧
  (∀ p q, knows (p ⇨ q) ≤ knows p ⇨ knows q) ∧
  (∀ p, knows p ≤ knows (knows p)) ∧
  (∀ p, (knows p)ᶜ ≤ knows ((knows p)ᶜ))

def FullForward : Prop := ∀ p : Content, p ≤ possible (knows p)

def MooreUnknowable : Prop :=
  (∀ p, moore p = ⊥) ∧ (∀ p, knows (moore p) = ⊥)

def DoubleNegatedConsequence : Prop := ∀ p : Content, p ≤ (knows p)ᶜᶜ

/-- All semantic laws and the same actual counterprofile hold jointly.
The two meta-level failures are non-forcing; ¬Kp is itself NOT forced.
Relevant object-language stability and excluded middle are explicitly unforced.
This changes the semantic profile, not any old frozen Challenge or EM floor. -/
def JointSurvivor : Prop :=
  FutureForcing ∧ OperatorsExact ∧ FrameProfile ∧ EpistemicLaws ∧
    FullForward ∧ MooreUnknowable ∧ DoubleNegatedConsequence ∧
    holds atom actual ∧ ¬ holds (knows atom) actual ∧
    ¬ holds (knows atom)ᶜ actual ∧ holds (knows atom)ᶜᶜ actual ∧
    ¬ holds ((knows atom)ᶜᶜ ⇨ knows atom) actual ∧
    ¬ holds (knows atom ⊔ (knows atom)ᶜ) actual

end TruthCore.Logic.IntuitionisticKnowability
