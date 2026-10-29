import TruthCore.Greek.Aristotle.SynonymousCause
namespace TruthCore.Greek.Aristotle.Metaphysics

/-- Metaphysics II.1, 993b24–26: a conservative pairwise consequence of
most-such, permitting ties. `AtLeastIn r c x` means that c is at least as r
as x. It is not identified with the existing strict `MoreIn` relation; the
connection to any concrete order and the shared account remain open. -/
def SynonymousCauseAtLeastReading {Entity : Sort u} {Respect : Sort v}
    (CausesIn : Entity → Entity → Respect → Prop)
    (AtLeastIn : Respect → Entity → Entity → Prop)
    {Sense : Sort w} (Holds : Entity → Respect → Sense → Prop) : Prop :=
  ∀ c x r, c ≠ x → CausesIn c x r →
    (∃ s, Holds c r s ∧ Holds x r s) → AtLeastIn r c x

/-- A two-entity same-account causal tie satisfies the at-least reading
while failing the strict reading. This is only a formal interpretation. -/
def SynonymousCauseTieControl : Prop :=
  ∃ (causes : Bool → Bool → Unit → Prop)
    (atLeast more : Unit → Bool → Bool → Prop)
    (holds : Bool → Unit → Unit → Prop),
    SynonymousCauseAtLeastReading causes atLeast holds ∧
    ¬ SynonymousCauseMoreSuchReading causes more holds ∧
    causes false true () ∧ holds false () () ∧ holds true () () ∧
    atLeast () false true ∧ atLeast () true false ∧ ¬ more () false true

end TruthCore.Greek.Aristotle.Metaphysics
