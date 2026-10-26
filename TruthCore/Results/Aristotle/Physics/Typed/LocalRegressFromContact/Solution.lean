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
  -- INF-ARIST-PHYS-VII-1-LOCAL-REGRESS-FROM-CONTACT
  rintro ⟨c, hInj, hChain⟩
  have hTouching : ∀ n, Touches (c (n + 1)) (c n) := by
    intro n
    obtain ⟨_, hPrimary, ⟨r, hLocal, hMoves⟩, _⟩ := hChain n
    exact hContact (c (n + 1)) (c n) r hLocal hPrimary hMoves
  obtain ⟨w, hw⟩ := hOne c hInj hTouching
  exact hImpossible w (hTraverse c w hInj hChain hw)

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
  -- every model below is the successor chain on `Nat`, every link local, primary and moved
  have succChain : ∀ n, LocalMovedMoverLink (fun _ : Unit => True) (fun (_ : Nat) _ => True)
      (fun y x (_ : Unit) => y = x + 1) (fun y x => y = x + 1) (n + 1) n :=
    fun n => ⟨Nat.succ_ne_self n, rfl, ⟨(), trivial, rfl⟩, ⟨(), trivial, trivial⟩⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- without contact: nothing touches, so nothing is composed and nothing traverses
    intro h
    exact h Nat Unit (fun _ => True) (fun _ _ => True) (fun y x _ => y = x + 1) (fun y x => y = x + 1)
      (fun _ _ => False) (fun _ _ => False) (fun _ => False)
      (fun _ _ hT => (hT 0).elim) (fun _ _ _ _ hw => hw.elim) (fun _ hw => hw)
      ⟨fun n => n, fun _ _ h => h, succChain⟩
  · -- without the one composite: contact holds, but nothing is made of the chain
    intro h
    exact h Nat Unit (fun _ => True) (fun _ _ => True) (fun y x _ => y = x + 1) (fun y x => y = x + 1)
      (fun _ _ => True) (fun _ _ => False) (fun _ => False)
      (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ hw => hw.elim) (fun _ hw => hw)
      ⟨fun n => n, fun _ _ h => h, succChain⟩
  · -- without the traversal premise: a composite exists but traverses nothing
    intro h
    exact h Nat Unit (fun _ => True) (fun _ _ => True) (fun y x _ => y = x + 1) (fun y x => y = x + 1)
      (fun _ _ => True) (fun _ _ => True) (fun _ => False)
      (fun _ _ _ _ _ _ => trivial) (fun _ _ _ => ⟨0, trivial⟩) (fun _ hw => hw)
      ⟨fun n => n, fun _ _ h => h, succChain⟩
  · -- without the impossibility premise: the composite does traverse
    intro h
    exact h Nat Unit (fun _ => True) (fun _ _ => True) (fun y x _ => y = x + 1) (fun y x => y = x + 1)
      (fun _ _ => True) (fun _ _ => True) (fun _ => True)
      (fun _ _ _ _ _ _ => trivial) (fun _ _ _ => ⟨0, trivial⟩) (fun _ _ _ _ _ => trivial)
      ⟨fun n => n, fun _ _ h => h, succChain⟩

end TruthCore.Results.Aristotle.Physics.Typed.LocalRegressFromContact
