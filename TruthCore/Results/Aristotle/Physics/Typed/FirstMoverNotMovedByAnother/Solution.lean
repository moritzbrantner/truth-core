import TruthCore.Greek.Aristotle.Physics.Typed.Motion
namespace TruthCore.Results.Aristotle.Physics.Typed.FirstMoverNotMovedByAnother
open TruthCore.Greek.Aristotle.Physics.Typed
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- *Physics* VIII.5, 256a13-21: something is moved; whatever is moved is moved by
something; and the mover relation is accessible at every being (an additional,
unattributed commitment, stronger than the source prohibition of infinitely many
distinct movers). So there cannot fail to be a mover not moved by another.

Suppose every mover is moved by another. Something is moved, so something moves.
By induction along the series of movers moved by another, no mover can exist:
a mover is moved by another (assumption), that other is a mover, hence also moved
by another, hence a link of the series below which, by the induction hypothesis,
no mover exists. -/
theorem firstMoverNotMovedByAnother {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (hSense : SomethingIsMovedReading MovedIn)
    (hMover : EveryMovedThingHasSomeMoverReading MovedIn MovesIn)
    (hRegress : NoInfiniteSeriesOfMoversMovedByAnotherReading MovesIn) :
    FirstMoverNotMovedByAnotherCannotBeLackingReading MovesIn := by
  -- INF-ARIST-PHYS-VIII-5-FIRST-MOVER-NOT-MOVED-BY-ANOTHER
  intro hNone
  have hAll : ∀ f, (∃ x r, MovesIn f x r) → ¬ ¬ MovedByAnother MovesIn f :=
    fun f hf hNot => hNone ⟨f, hf, hNot⟩
  have noMover : ∀ y, Acc (MoverMovedByAnotherLink MovesIn) y →
      (∃ x r, MovesIn y x r) → False := by
    intro y hAcc
    induction hAcc with
    | intro y _ ih =>
      intro hy
      apply hAll y hy
      rintro ⟨z, r, hNe, hz⟩
      apply hAll z ⟨y, r, hz⟩
      intro hzByAnother
      exact ih z ⟨hNe, ⟨r, hz⟩, hzByAnother⟩ ⟨y, r, hz⟩
  obtain ⟨x, r, hMoved⟩ := hSense
  obtain ⟨y, r', hy⟩ := hMover x r hMoved
  exact noMover y (hRegress y) ⟨x, r', hy⟩

/-- Each of the three premises is needed. Without sensible motion, nothing moves;
without a mover for every moved thing, something is moved by nothing; without the
regress premise, each number is moved by its successor, so every mover is moved
by another. -/
theorem premisesNeeded :
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop),
      EveryMovedThingHasSomeMoverReading MovedIn MovesIn →
      NoInfiniteSeriesOfMoversMovedByAnotherReading MovesIn →
      FirstMoverNotMovedByAnotherCannotBeLackingReading MovesIn) ∧
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop),
      SomethingIsMovedReading MovedIn →
      NoInfiniteSeriesOfMoversMovedByAnotherReading MovesIn →
      FirstMoverNotMovedByAnotherCannotBeLackingReading MovesIn) ∧
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop),
      SomethingIsMovedReading MovedIn →
      EveryMovedThingHasSomeMoverReading MovedIn MovesIn →
      FirstMoverNotMovedByAnotherCannotBeLackingReading MovesIn) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply h Unit Unit (fun _ _ => False) (fun _ _ _ => False)
      (fun _ _ hm => hm.elim) (fun x => Acc.intro x (fun _ ⟨_, ⟨_, hm⟩, _⟩ => hm.elim))
    rintro ⟨_, ⟨_, _, hm⟩, _⟩
    exact hm
  · intro h
    apply h Unit Unit (fun _ _ => True) (fun _ _ _ => False)
      ⟨(), (), trivial⟩ (fun x => Acc.intro x (fun _ ⟨_, ⟨_, hm⟩, _⟩ => hm.elim))
    rintro ⟨_, ⟨_, _, hm⟩, _⟩
    exact hm
  · intro h
    apply h Nat Unit (fun _ _ => True) (fun y x _ => y = x + 1)
      ⟨0, (), trivial⟩ (fun x _ _ => ⟨x + 1, (), rfl⟩)
    rintro ⟨f, ⟨x, _, hf⟩, hNot⟩
    exact hNot ⟨f + 1, (), Nat.succ_ne_self f, rfl⟩

end TruthCore.Results.Aristotle.Physics.Typed.FirstMoverNotMovedByAnother
