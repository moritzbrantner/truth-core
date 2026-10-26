/-! A motion requirement in the predecessor survey of Physics VIII.1. -/

namespace TruthCore.Greek.Aristotle.Physics.Typed

universe u v w

/-- Aristotle, *Physics* VIII.1, 250b18–23: the generations and destructions
of worlds must occur with motion. This isolates the parenthetical ground in
the survey of cosmologists who posit infinitely many worlds; it does not adopt
their cosmology or infer everlasting motion.

`CosmicGenerationOrDestruction e` marks an occurrence of a world's coming to be
or perishing. `Accompanies e x r` ties a subject's physical motion in a respect
to that occurrence; no temporal precedence or identity with generation itself
is asserted. `MovedIn` and `IsPhysicalRespect` retain the existing typed Physics
meanings. This is a source commitment, not a verified derivation.
-/
def CosmicGenerationDestructionRequiresMotionReading
    {Event : Sort u} {Being : Sort v} {Respect : Sort w}
    (CosmicGenerationOrDestruction : Event → Prop)
    (IsPhysicalRespect : Respect → Prop)
    (MovedIn : Being → Respect → Prop)
    (Accompanies : Event → Being → Respect → Prop) : Prop :=
  ∀ e, CosmicGenerationOrDestruction e →
    ∃ x r, IsPhysicalRespect r ∧ MovedIn x r ∧ Accompanies e x r

end TruthCore.Greek.Aristotle.Physics.Typed
