module

public import TruthCore.Greek.Aristotle.Physics.LocalContactComposition

@[expose] public section
namespace TruthCore.Results.Aristotle.Physics.LocalContactComposition.Strength
open TruthCore.Greek.Aristotle.Physics.Typed
open TruthCore.Greek.Aristotle.Physics.LocalContactComposition

/-- Analyst local-scope consequence; original source reading and frozen result unchanged. -/
theorem globalImpliesLocal {B R : Type} (IsLocal : R → Prop) (MovedIn : B → R → Prop)
    (MovesIn : B → B → R → Prop) (MovesPrimarily Touches : B → B → Prop)
    (ComposedOf : B → (Nat → B) → Prop)
    (h : TouchingChainFormsOneReading Touches ComposedOf) :
    LocalTouchingChainFormsOne IsLocal MovedIn MovesIn MovesPrimarily Touches ComposedOf := by
  intro c hInj _ hTouch
  exact h c hInj hTouch

end TruthCore.Results.Aristotle.Physics.LocalContactComposition.Strength
