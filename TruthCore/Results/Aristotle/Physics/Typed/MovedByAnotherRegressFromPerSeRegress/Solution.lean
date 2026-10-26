import TruthCore.Greek.Aristotle.Physics.Typed.Motion
namespace TruthCore.Results.Aristotle.Physics.Typed.MovedByAnotherRegressFromPerSeRegress
open TruthCore.Greek.Aristotle.Physics.Typed
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- The additional accessibility commitment for the VIII.5 mover relation follows
from the *prima via* accessibility premise, given
*Physics* III.3. A link of VIII.5's series is a mover `y` of `x`, other than `x`,
that some other thing moves; by III.3 `y` is then itself being moved, so by the
second-movers premise `y` moves `x` as a per se link. Every being is accessible
under the per se links, hence under VIII.5's links. This proves the stronger
commitment conditionally; it is not an attribution of accessibility to Aristotle. -/
theorem movedByAnotherRegressFromPerSeRegress {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (MovesAsMoved : Being → Being → Prop)
    (hInMoved : MovingIsInTheMovedReading MovesIn MovedIn)
    (hPerSe : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved) :
    NoInfiniteSeriesOfMoversMovedByAnotherReading MovesIn := by
  -- INF-ARIST-PHYS-VIII-5-REGRESS-FROM-PER-SE-REGRESS
  intro x
  induction hRegress x with
  | intro x _ ih =>
    apply Acc.intro x
    rintro y ⟨hNe, ⟨r, hMoves⟩, ⟨z, r', _, hz⟩⟩
    exact ih y (hPerSe y x r hNe hMoves ⟨r', hInMoved z y r' hz⟩)

/-- Each of the three premises is needed. Every model has each number moved by its
successor, so VIII.5's series is infinite. Without III.3 nothing is being moved,
so the second-movers premise makes no link per se; without the second-movers
premise no link is per se; without the regress premise the per se series is the
successor relation itself. -/
theorem premisesNeeded :
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (MovesAsMoved : Being → Being → Prop),
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved →
      NoInfinitePerSeMoverSeriesReading MovesAsMoved →
      NoInfiniteSeriesOfMoversMovedByAnotherReading MovesIn) ∧
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (MovesAsMoved : Being → Being → Prop),
      MovingIsInTheMovedReading MovesIn MovedIn →
      NoInfinitePerSeMoverSeriesReading MovesAsMoved →
      NoInfiniteSeriesOfMoversMovedByAnotherReading MovesIn) ∧
    (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (MovesAsMoved : Being → Being → Prop),
      MovingIsInTheMovedReading MovesIn MovedIn →
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved →
      NoInfiniteSeriesOfMoversMovedByAnotherReading MovesIn) := by
  -- in each model the series of movers moved by another is the successor relation
  have notAcc : ∀ n : Nat, ¬ Acc (MoverMovedByAnotherLink
      (fun y x (_ : Unit) => y = x + 1)) n := by
    intro n hAcc
    induction hAcc with
    | intro x _ ih =>
      exact ih (x + 1)
        ⟨Nat.succ_ne_self x, ⟨(), rfl⟩, ⟨x + 1 + 1, (), Nat.succ_ne_self (x + 1), rfl⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact notAcc 0 (h Nat Unit (fun _ _ => False) (fun y x _ => y = x + 1)
      (fun _ _ => False) (fun _ _ _ _ _ ⟨_, hm⟩ => hm.elim)
      (fun x => Acc.intro x (fun _ hf => hf.elim)) 0)
  · intro h
    exact notAcc 0 (h Nat Unit (fun _ _ => True) (fun y x _ => y = x + 1)
      (fun _ _ => False) (fun _ _ _ _ => trivial)
      (fun x => Acc.intro x (fun _ hf => hf.elim)) 0)
  · intro h
    exact notAcc 0 (h Nat Unit (fun _ _ => True) (fun y x _ => y = x + 1)
      (fun y x => y = x + 1) (fun _ _ _ _ => trivial)
      (fun _ _ _ _ hMoves _ => hMoves) 0)

end TruthCore.Results.Aristotle.Physics.Typed.MovedByAnotherRegressFromPerSeRegress
