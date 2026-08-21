/-!
Source-derived claims from Aristotle's *Categories*.
-/

namespace TruthCore.Greek.Aristotle.Categories

universe u

/--
Definitional reading of Aristotle, *Categories* V, 2a11-14: a primary substance is
neither said of a subject nor in a subject.

`SaidOf` and `In` remain two supplied relations. This preserves the distinction prepared
in I.2, 1a20-1b9, where being in a subject excludes being a part and requires inability to
exist apart from that subject. The declaration therefore does not identify either relation
with a modern predicate, instantiation, inherence, parthood, or existential dependence.
It also leaves the passage's examples (the individual human and horse) illustrative rather
than adding a separate theory of individuality.

The continuation at 2a14-19 calls species and genera secondary substances; that further
classification is not included in this atomic primary-substance reading.

Source: Aristotle, *Categories* V, 2a11-19; immediate conceptual context I.2, 1a20-1b9
(Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg006`.
-/
def PrimarySubstanceBySubjectRelationsReading
    {Entity : Type u}
    (IsPrimarySubstance : Entity → Prop)
    (SaidOf : Entity → Entity → Prop)
    (In : Entity → Entity → Prop) : Prop :=
  ∀ entity,
    IsPrimarySubstance entity ↔
      (¬ ∃ subject, SaidOf entity subject) ∧
        ¬ ∃ subject, In entity subject

end TruthCore.Greek.Aristotle.Categories
