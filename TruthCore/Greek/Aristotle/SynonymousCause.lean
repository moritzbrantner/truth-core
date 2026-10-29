import TruthCore.Greek.Aristotle.Metaphysics

namespace TruthCore.Greek.Aristotle.Metaphysics

/-- Metaphysics II.1, 993b24–26: restricted pairwise reading of the
cause-most-such sentence. `Holds c r s` means that cause c has quality r under defining account s.
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

/-- A three-entity interpretation has one same-sense causal edge with a
comparison and a second, non-same-sense causal edge without one. This is a
logical countermodel to the converse, not a claim of metaphysical possibility. -/
theorem synonymous_does_not_imply_unrestricted :
    ∃ (causes : Fin 3 → Fin 3 → Unit → Prop)
      (more : Unit → Fin 3 → Fin 3 → Prop)
      (holds : Fin 3 → Unit → Bool → Prop),
      SynonymousCauseMoreSuchReading causes more holds ∧
      ¬ CauseOfQualityInAnotherIsMoreSuchReading causes more := by
  refine ⟨fun c x _ => (c = 0 ∧ x = 1) ∨ (c = 1 ∧ x = 2),
    fun _ c x => c = 0 ∧ x = 1,
    fun c _ s => (c = 0 ∧ s = false) ∨ (c = 1 ∧ s = false) ∨ (c = 2 ∧ s = true), ?_, ?_⟩
  · intro c x r _ hc hs
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · rcases hs with ⟨s, h1, h2⟩
      cases s <;> simp at h1 h2
  · intro h
    have bad := h 1 2 () (by decide) (Or.inr ⟨rfl, rfl⟩)
    exact (by decide : ¬ ((1 : Fin 3) = 0 ∧ (2 : Fin 3) = 1)) bad

end TruthCore.Greek.Aristotle.Metaphysics
