module

public import TruthCore.Causality.SpineRivalsStageOne

/-!
# The walk along the modal spine: the frame premises

Analyst formulations for the walk in `docs/notes/modal-spine.md`; attribution
deferred. This module holds what a rival of a frame premise must also accept.
Nothing here is asserted of reality: a definition names a frame shape, and the
results show which shape a rival is committed to under the other frame premise.

* `ActualAloneNotSelfAccessible`: the selected world does not access itself,
  accesses some world, and every world it accesses does access itself. Read
  alethically: the actual world is the one world in view that is not possible
  relative to itself. It is a shape of the accessibility relation, not a claim
  about what exists; it differs from a frame in which no world accesses itself.
-/

@[expose] public section

namespace TruthCore.Causality.SpineWalkFrame

open TruthCore.German.Kant.CosmologicalInference

/-- The selected world does not access itself, accesses some world, and every
world it accesses accesses itself. -/
def ActualAloneNotSelfAccessible {W B : Type} (m : Ontic W B) (w : W) : Prop :=
  ¬ m.frame.access w w ∧ (∃ v, m.frame.access w v) ∧
    ∀ v, m.frame.access w v → m.frame.access v v

end TruthCore.Causality.SpineWalkFrame
