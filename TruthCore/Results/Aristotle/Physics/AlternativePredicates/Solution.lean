import TruthCore.Greek.Aristotle.Physics

namespace TruthCore.Results.Aristotle.Physics.AlternativePredicates

open TruthCore.Greek.Aristotle.Physics

universe u

/--
If difference, inequality, and non-being each can hold without necessitating motion, none of
them can be coextensive with motion.
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
  rcases hNonNecessity with ⟨hDifferent, hUnequal, hNonBeing⟩
  constructor
  · intro hSame
    apply hDifferent
    intro entity hDifferentEntity
    exact (hSame entity).mp hDifferentEntity
  constructor
  · intro hSame
    apply hUnequal
    intro entity hUnequalEntity
    exact (hSame entity).mp hUnequalEntity
  · intro hSame
    apply hNonBeing
    intro entity hNonBeingEntity
    exact (hSame entity).mp hNonBeingEntity

end TruthCore.Results.Aristotle.Physics.AlternativePredicates
