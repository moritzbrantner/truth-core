import TruthCore.Greek.Aristotle.Physics.BookV.Chapter5

namespace TruthCore.Results.Aristotle.Physics.ReverseMotionsContrary

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's contrary-goal argument in *Physics* V.5, 229a20-229b8. -/
theorem reverseMotionsContrary
    (GoalsContrary MotionsContrary MotionsNamedMoreFromGoals : Prop)
    (hGoalGrounds :
      GoalRatherThanSourceGroundsMotionContrarietyReading
        GoalsContrary MotionsContrary MotionsNamedMoreFromGoals)
    (hReverseGoals : ReverseMotionsHaveContraryGoalsReading GoalsContrary) :
    ReverseMotionsBetweenContrariesAreContraryReading MotionsContrary := by
  exact hGoalGrounds.1 hReverseGoals

end TruthCore.Results.Aristotle.Physics.ReverseMotionsContrary
