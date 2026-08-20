/-!
Source-derived claims from Plato's *Timaeus*.

These declarations encode readings of passages; they do not assert that the readings are
historically exhaustive or philosophically true.
-/

namespace TruthCore.Greek.Plato.Timaeus

universe u

/--
Broad reading of *Timaeus* 28a: anything that comes to be has some cause.

Source: Plato, *Timaeus* 28a (Stephanus pagination).
CTS work: `urn:cts:greekLit:tlg0059.tlg031`.

This deliberately says only that a cause exists. It does not build distinctness, temporal
priority, agency, or uniqueness into the word "cause".
-/
def CausePrinciple
    {Entity : Type u}
    (ComesToBe : Entity → Prop)
    (Causes : Entity → Entity → Prop) : Prop :=
  ∀ x, ComesToBe x → ∃ y, Causes y x

/--
Stronger reading of *Timaeus* 28a: anything that comes to be has a cause distinct from it.

This is kept as a separate interpretation rather than silently strengthening `CausePrinciple`.
Source: Plato, *Timaeus* 28a.
CTS work: `urn:cts:greekLit:tlg0059.tlg031`.
-/
def DistinctCausePrinciple
    {Entity : Type u}
    (ComesToBe : Entity → Prop)
    (Causes : Entity → Entity → Prop) : Prop :=
  ∀ x, ComesToBe x → ∃ y, y ≠ x ∧ Causes y x

/--
Minimal reading of *Timaeus* 28b-28c used by the seed argument: the cosmos is among
what has come to be.

Source: Plato, *Timaeus* 28b-28c.
CTS work: `urn:cts:greekLit:tlg0059.tlg031`.
-/
def CosmosGenerated
    {Entity : Type u}
    (ComesToBe : Entity → Prop)
    (cosmos : Entity) : Prop :=
  ComesToBe cosmos

end TruthCore.Greek.Plato.Timaeus
