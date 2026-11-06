import TruthCore.Greek.Aristotle.Physics.LocalContactComposition

namespace TruthCore.Results.Aristotle.Physics.LocalContactComposition.Regress
open TruthCore.Greek.Aristotle.Physics.Typed
open TruthCore.Greek.Aristotle.Physics.LocalContactComposition

/-- Analyst local-scope consequence; original source reading and frozen result unchanged. -/
theorem localCompositionRegress {B R : Type} (IsLocal : R → Prop) (MovedIn : B → R → Prop)
    (MovesIn : B → B → R → Prop) (MovesPrimarily Touches : B → B → Prop)
    (ComposedOf : B → (Nat → B) → Prop)
    (Traverses : B → Prop)
    (hContact : PrimaryLocalMoverTouchesReading IsLocal MovesIn MovesPrimarily Touches)
    (hOne : LocalTouchingChainFormsOne IsLocal MovedIn MovesIn MovesPrimarily Touches ComposedOf)
    (hTraverse : OneOfInfiniteLocalChainTraversesInfiniteReading IsLocal MovedIn MovesIn
      MovesPrimarily ComposedOf Traverses)
    (hImpossible : NoInfiniteTraversalInFiniteTimeReading Traverses) :
    NoInfiniteLocalMovedMoverChainReading IsLocal MovedIn MovesIn MovesPrimarily := by
  sorry

end TruthCore.Results.Aristotle.Physics.LocalContactComposition.Regress
