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
  sorry

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
  sorry

end TruthCore.Results.Aristotle.Physics.Typed.MovedByAnotherRegressFromPerSeRegress
