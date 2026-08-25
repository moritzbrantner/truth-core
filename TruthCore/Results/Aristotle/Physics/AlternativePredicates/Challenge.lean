import TruthCore.Greek.Aristotle.Physics

namespace TruthCore.Results.Aristotle.Physics.AlternativePredicates

open TruthCore.Greek.Aristotle.Physics

universe u

/--
If difference, inequality, and non-being each can hold without necessitating motion, none of
them can be coextensive with motion.

This theorem verifies only that formal rejection step; the source premise remains a distinct
scholarly claim.
-/
theorem motionNotIdenticalWithAlternatives
    {Entity : Type u}
    (Different : Entity → Prop)
    (Unequal : Entity → Prop)
    (NonBeing : Entity → Prop)
    (IsMoved : Entity → Prop)
    (hNonNecessity :
      AlternativePredicatesDoNotNecessitateMotionReading
        Different Unequal NonBeing IsMoved) :
    MotionNotIdenticalWithAlternativePredicatesReading
      Different Unequal NonBeing IsMoved := by
  sorry

end TruthCore.Results.Aristotle.Physics.AlternativePredicates
