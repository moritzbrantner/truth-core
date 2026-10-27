/-!
Hume, *Treatise* I.3.6 §7 (SBN 89–90): "The same principle cannot be both the
cause and effect of another; and this is, perhaps, the only proposition
concerning that relation, which is either intuitively or demonstratively
certain."

Source witness: HUME-TREATISE-I-3-6 (Hume Texts Online, hash-pinned).
-/

namespace TruthCore.Modern.Hume.CauseEffectAsymmetry

/-- Hume's asymmetry maxim (*Treatise* I.3.6 §7): nothing is both the cause and
the effect of another thing.

`cause a b` reads "a is a cause of b" in Hume's relation of cause and effect
(DEF-HUME-CAUSE-EFFECT-RELATION); the relation is a parameter and is not
interpreted. "Another" is kept: the maxim is stated for two distinct relata, so
it says nothing about self-causation. The modal "cannot" and Hume's claim that
the maxim is (perhaps uniquely) intuitively or demonstratively certain are not
formalized; only the non-modal content is, which is weaker than the sentence.
It excludes two-step cycles only, not longer ones (see the result
HUME-NO-MUTUAL-CAUSE-FROM-NO-LOOPS). -/
def NoMutualCauseReading {Entity : Type} (cause : Entity → Entity → Prop) : Prop :=
  ∀ x y, x ≠ y → ¬ (cause x y ∧ cause y x)

end TruthCore.Modern.Hume.CauseEffectAsymmetry
