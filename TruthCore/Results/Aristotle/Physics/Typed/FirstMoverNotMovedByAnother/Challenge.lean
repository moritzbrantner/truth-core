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
  sorry

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
  sorry

end TruthCore.Results.Aristotle.Physics.Typed.FirstMoverNotMovedByAnother
