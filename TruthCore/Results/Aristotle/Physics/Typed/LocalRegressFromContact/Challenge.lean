import TruthCore.Greek.Aristotle.Physics.Typed.Motion
namespace TruthCore.Results.Aristotle.Physics.Typed.LocalRegressFromContact
open TruthCore.Greek.Aristotle.Physics.Typed

/-- *Physics* VII.1's repaired regress argument (242b23-243a2). Suppose an infinite
chain in which each member is moved in local motion by the next, a primary mover of
it that is itself moved in local motion. Each primary local mover touches what it
moves, so the chain is a chain of things in contact, and some one thing is made of
them all. That one thing would go through an infinite motion in a finite time,
which nothing does. So there is no such chain. -/
theorem localRegressFromContact {Being : Type} {Respect : Type}
    (IsLocal : Respect → Prop)
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (MovesPrimarily Touches : Being → Being → Prop)
    (ComposedOf : Being → (Nat → Being) → Prop)
    (TraversesInfiniteInFiniteTime : Being → Prop)
    (hContact : PrimaryLocalMoverTouchesReading IsLocal MovesIn MovesPrimarily Touches)
    (hOne : TouchingChainFormsOneReading Touches ComposedOf)
    (hTraverse : OneOfInfiniteLocalChainTraversesInfiniteReading IsLocal MovedIn MovesIn
      MovesPrimarily ComposedOf TraversesInfiniteInFiniteTime)
    (hImpossible : NoInfiniteTraversalInFiniteTimeReading TraversesInfiniteInFiniteTime) :
    NoInfiniteLocalMovedMoverChainReading IsLocal MovedIn MovesIn MovesPrimarily := by
  sorry

/-- Each of the four premises is needed. Without contact, the infinite successor
chain touches nowhere; without the one composite, nothing is made of it; without
the traversal premise, the composite traverses nothing; without the impossibility
premise, it traverses an infinite motion in a finite time. -/
theorem premisesNeeded :
    (¬ ∀ (Being Respect : Type) (IsLocal : Respect → Prop) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (MovesPrimarily Touches : Being → Being → Prop)
        (ComposedOf : Being → (Nat → Being) → Prop) (Traverses : Being → Prop),
      TouchingChainFormsOneReading Touches ComposedOf →
      OneOfInfiniteLocalChainTraversesInfiniteReading IsLocal MovedIn MovesIn MovesPrimarily
        ComposedOf Traverses →
      NoInfiniteTraversalInFiniteTimeReading Traverses →
      NoInfiniteLocalMovedMoverChainReading IsLocal MovedIn MovesIn MovesPrimarily) ∧
    (¬ ∀ (Being Respect : Type) (IsLocal : Respect → Prop) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (MovesPrimarily Touches : Being → Being → Prop)
        (ComposedOf : Being → (Nat → Being) → Prop) (Traverses : Being → Prop),
      PrimaryLocalMoverTouchesReading IsLocal MovesIn MovesPrimarily Touches →
      OneOfInfiniteLocalChainTraversesInfiniteReading IsLocal MovedIn MovesIn MovesPrimarily
        ComposedOf Traverses →
      NoInfiniteTraversalInFiniteTimeReading Traverses →
      NoInfiniteLocalMovedMoverChainReading IsLocal MovedIn MovesIn MovesPrimarily) ∧
    (¬ ∀ (Being Respect : Type) (IsLocal : Respect → Prop) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (MovesPrimarily Touches : Being → Being → Prop)
        (ComposedOf : Being → (Nat → Being) → Prop) (Traverses : Being → Prop),
      PrimaryLocalMoverTouchesReading IsLocal MovesIn MovesPrimarily Touches →
      TouchingChainFormsOneReading Touches ComposedOf →
      NoInfiniteTraversalInFiniteTimeReading Traverses →
      NoInfiniteLocalMovedMoverChainReading IsLocal MovedIn MovesIn MovesPrimarily) ∧
    (¬ ∀ (Being Respect : Type) (IsLocal : Respect → Prop) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (MovesPrimarily Touches : Being → Being → Prop)
        (ComposedOf : Being → (Nat → Being) → Prop) (Traverses : Being → Prop),
      PrimaryLocalMoverTouchesReading IsLocal MovesIn MovesPrimarily Touches →
      TouchingChainFormsOneReading Touches ComposedOf →
      OneOfInfiniteLocalChainTraversesInfiniteReading IsLocal MovedIn MovesIn MovesPrimarily
        ComposedOf Traverses →
      NoInfiniteLocalMovedMoverChainReading IsLocal MovedIn MovesIn MovesPrimarily) := by
  sorry

end TruthCore.Results.Aristotle.Physics.Typed.LocalRegressFromContact
