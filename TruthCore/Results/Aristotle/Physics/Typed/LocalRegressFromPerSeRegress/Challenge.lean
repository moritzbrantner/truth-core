import TruthCore.Greek.Aristotle.Physics.Typed.Motion
namespace TruthCore.Results.Aristotle.Physics.Typed.LocalRegressFromPerSeRegress
open TruthCore.Greek.Aristotle.Physics.Typed
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- *Physics* VII.1's restricted regress follows from the *prima via*'s regress
premise. A link of VII.1's chain is a mover other than the moved thing that moves
it and is itself being moved; by the *prima via*'s second-movers premise it is a
per se link, and the per se series has no infinite descent. -/
theorem localRegressFromPerSeRegress {Being : Type} {Respect : Type}
    (IsLocal : Respect → Prop)
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (MovesPrimarily : Being → Being → Prop)
    (MovesAsMoved : Being → Being → Prop)
    (hPerSe : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved) :
    NoInfiniteLocalMovedMoverChainReading IsLocal MovedIn MovesIn MovesPrimarily := by
  sorry

/-- Both premises are needed. Every model is the successor chain on `Nat`, each
number moving its predecessor locally and primarily and being moved: without the
second-movers premise no link is per se; without the regress premise the per se
series is the successor relation itself. -/
theorem premisesNeeded :
    (¬ ∀ (Being Respect : Type) (IsLocal : Respect → Prop) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (MovesPrimarily MovesAsMoved : Being → Being → Prop),
      NoInfinitePerSeMoverSeriesReading MovesAsMoved →
      NoInfiniteLocalMovedMoverChainReading IsLocal MovedIn MovesIn MovesPrimarily) ∧
    (¬ ∀ (Being Respect : Type) (IsLocal : Respect → Prop) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (MovesPrimarily MovesAsMoved : Being → Being → Prop),
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved →
      NoInfiniteLocalMovedMoverChainReading IsLocal MovedIn MovesIn MovesPrimarily) := by
  sorry

/-- The restricted regress is strictly weaker than the per se regress, even
granted the second-movers premise: when no respect is local, there is no local
chain at all, while the per se series is the infinite successor relation. So
VII.1's conclusion cannot stand in for the *prima via*'s regress premise. -/
theorem restrictedRegressIsWeaker :
    ¬ ∀ (Being Respect : Type) (IsLocal : Respect → Prop) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (MovesPrimarily MovesAsMoved : Being → Being → Prop),
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved →
      NoInfiniteLocalMovedMoverChainReading IsLocal MovedIn MovesIn MovesPrimarily →
      NoInfinitePerSeMoverSeriesReading MovesAsMoved := by
  sorry

end TruthCore.Results.Aristotle.Physics.Typed.LocalRegressFromPerSeRegress
