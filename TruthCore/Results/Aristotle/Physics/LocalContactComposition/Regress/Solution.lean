module

public import TruthCore.Greek.Aristotle.Physics.LocalContactComposition

@[expose] public section
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
  rintro ⟨c, hInj, hChain⟩
  have hTouching : ∀ n, Touches (c (n+1)) (c n) := by
    intro n
    obtain ⟨_, hPrimary, ⟨r, hLocal, hMoves⟩, _⟩ := hChain n
    exact hContact (c (n+1)) (c n) r hLocal hPrimary hMoves
  obtain ⟨w, hw⟩ := hOne c hInj hChain hTouching
  exact hImpossible w (hTraverse c w hInj hChain hw)

end TruthCore.Results.Aristotle.Physics.LocalContactComposition.Regress
