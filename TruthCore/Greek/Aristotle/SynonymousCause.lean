import TruthCore.Greek.Aristotle.Metaphysics

namespace TruthCore.Greek.Aristotle.Metaphysics

/-- Strict strengthening of the restricted pairwise reading of Metaphysics II.1,
993b24–26, not attributed to the source: most-such need not exclude ties. `Holds c r s` means that cause c has quality r under defining account s.
Both cause and effect must have the quality under one shared account. It is
an explicit interpretive condition, not a definition of causal or analogical
predication; neither its extension nor its applicability to being is assumed. -/
def SynonymousCauseMoreSuchReading {Entity : Sort u} {Respect : Sort v}
    (CausesIn : Entity → Entity → Respect → Prop)
    (MoreIn : Respect → Entity → Entity → Prop)
    {Sense : Sort w} (Holds : Entity → Respect → Sense → Prop) : Prop :=
  ∀ c x r, c ≠ x → CausesIn c x r →
    (∃ s, Holds c r s ∧ Holds x r s) → MoreIn r c x

/-- The unrestricted premise implies the restricted reading, for any interpretation
of synonymy; the converse requires an additional assumption. -/
theorem unrestricted_implies_synonymous {Entity : Sort u} {Respect : Sort v}
    (causes : Entity → Entity → Respect → Prop)
    (more : Respect → Entity → Entity → Prop)
    {Sense : Sort w} (holds : Entity → Respect → Sense → Prop)
    (h : CauseOfQualityInAnotherIsMoreSuchReading causes more) :
    SynonymousCauseMoreSuchReading causes more holds := by
  intro c x r hne hc _
  exact h c x r hne hc

/-- Explicit finite points avoid the axiom-bearing Fin numeral instance. -/
def scopePoint0 : Fin 3 := ⟨0, Nat.zero_lt_succ 2⟩
def scopePoint1 : Fin 3 := ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩
def scopePoint2 : Fin 3 := ⟨2, Nat.lt_succ_self 2⟩

/-- A finite control with a same-account causal edge and a changed-account
causal edge. The restricted comparison holds, the broad comparison fails, and
both edges and their account profiles are explicit. This is a logical model,
not an assertion of metaphysical possibility. -/
def SynonymyScopeControl : Prop :=
  ∃ (causes : Fin 3 → Fin 3 → Unit → Prop)
    (more : Unit → Fin 3 → Fin 3 → Prop)
    (holds : Fin 3 → Unit → Bool → Prop),
    SynonymousCauseMoreSuchReading causes more holds ∧
    ¬ CauseOfQualityInAnotherIsMoreSuchReading causes more ∧
    causes scopePoint0 scopePoint1 () ∧ (∃ s, holds scopePoint0 () s ∧ holds scopePoint1 () s) ∧ more () scopePoint0 scopePoint1 ∧
    causes scopePoint1 scopePoint2 () ∧ (¬ ∃ s, holds scopePoint1 () s ∧ holds scopePoint2 () s) ∧ ¬ more () scopePoint1 scopePoint2

end TruthCore.Greek.Aristotle.Metaphysics
