import TruthCore.Alternatives.ActPotencyRegress

/-! Named registration interfaces for the branch's existing mixed-token priority
proof. These are OPEN analyst premises, not new source readings or an assertion
that simple priority of beings extends to existence tokens and acts. No new
priority relation or ontology is defined. -/
namespace TruthCore.Causality.ExistentialSelfActualization
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Alternatives.ActPotencyRegress

/-- An occurring act presupposes the existence-token of its bearer in the
selected mixed priority relation. This is not temporal precedence. -/
def BearerPrior (Occurs : E → Prop) (bearer : E → B)
    (Prior : Sum B E → Sum B E → Prop) : Prop :=
  ∀ a, Occurs a → Prior (.inl (bearer a)) (.inr a)

/-- An occurring existence-producing act precedes its product's existence-token.
The interpretation as genuine existential production is an open commitment. -/
def ProductPrior (Occurs : E → Prop) (produces : E → B → Prop)
    (Prior : Sum B E → Sum B E → Prop) : Prop :=
  ∀ a x, Occurs a → produces a x → Prior (.inr a) (.inl x)

/-- The mixed-token relation is irreflexive. This separate premise does not
follow merely by reusing the Second Way's logical property template. -/
def IrreflexivePriority (Prior : Sum B E → Sum B E → Prop) : Prop :=
  NothingPriorToItselfReading Prior

/-- Transitivity on the SAME mixed-token relation; it is not inferred from
irreflexivity, a temporal order, or transitivity of another explanatory relation. -/
def TransitivePriority (Prior : Sum B E → Sum B E → Prop) : Prop :=
  SimplePriorityTransitiveReading Prior

/-- No occurring act produces the existence of its own bearer. This does not
exclude every intrinsic reason, self-maintenance or self-change. -/
def NoSelfProduction (Occurs : E → Prop) (bearer : E → B)
    (produces : E → B → Prop) : Prop :=
  ∀ a, Occurs a → ¬ produces a (bearer a)

/-- Existing omission-edge controls and an inhabited positive model satisfying
all four named interfaces with an occurring productive act. No metaphysical
possibility or independent adequacy is asserted. -/
def Controls : Prop :=
  (∃ Prior : Sum Unit Unit → Sum Unit Unit → Prop,
    IrreflexivePriority Prior ∧ Prior (.inl ()) (.inr ()) ∧ Prior (.inr ()) (.inl ())) ∧
  (∃ Prior : Sum Unit Unit → Sum Unit Unit → Prop,
    TransitivePriority Prior ∧ Prior (.inl ()) (.inr ()) ∧ Prior (.inr ()) (.inl ())) ∧
  (∃ (Occurs : Unit → Prop) (bearer : Unit → Bool) (produces : Unit → Bool → Prop)
      (Prior : Sum Bool Unit → Sum Bool Unit → Prop),
    BearerPrior Occurs bearer Prior ∧ ProductPrior Occurs produces Prior ∧
    IrreflexivePriority Prior ∧ TransitivePriority Prior ∧ Occurs () ∧ produces () false)

end TruthCore.Causality.ExistentialSelfActualization
