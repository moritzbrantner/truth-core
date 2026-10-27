import TruthCore.Greek.Plato.Forms

/-!
A bounded reading of Proclus, Elements of Theology proposition 2, consulted in
Thomas Taylor's 1816 translation, vol. II p. 301; witness PROCLUS-ET-1-13-TAYLOR.

The shared entity, participation and predication interface is reused because it
can express the distinction without building nonidentity into the entity types.
This does not identify Proclus's One with a Platonic Form, assert FormOf, or
transfer any of the Platonic theory commitments. The entity `one` and quality
`unity` remain independent parameters. No theorem defends this source reading.
-/
namespace TruthCore.Greek.Proclus.ElementsTheology

open TruthCore.Greek.Plato.Forms

universe u v

/-- Proposition 2, bounded identity/predication reading: a participant receives
unity but is not the One itself. Taylor's 'one and not one' is not represented
as P ∧ ¬P in a single sense. This projection does not encode the full content of
'of itself not one', a theory of essential determinations, or a mechanism by
which participation produces unity. Both conjuncts are attributed commitments,
not conclusions proved here. -/
def ParticipantUnityContrast {Entity : Type u} {Quality : Type v}
    (s : Vocabulary Entity Quality) (one : Entity) (unity : Quality) : Prop :=
  ∀ x, s.Participates x one → s.Exemplifies x unity ∧ x ≠ one

end TruthCore.Greek.Proclus.ElementsTheology
