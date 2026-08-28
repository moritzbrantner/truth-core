import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter5

namespace TruthCore.Results.Aristotle.Physics.FirstCompletionTimeIndivisible
open TruthCore.Greek.Aristotle.Physics
/-- Aristotle's completion-boundary reductio in *Physics* VI.5, 235b30-236a5. -/
theorem firstCompletionTimeIndivisible
    (CompletionTimeIsPrimary CompletionTimeDivisible : Prop)
    (hPrimary : FirstCompletionTimePrimaryReading CompletionTimeIsPrimary)
    (hDivisibleNotPrimary : DivisibleCompletionTimeWouldNotBePrimaryReading
      CompletionTimeDivisible CompletionTimeIsPrimary) :
    FirstCompletionTimeIndivisibleReading CompletionTimeDivisible := by
  intro hDivisible
  exact hDivisibleNotPrimary hDivisible hPrimary
end TruthCore.Results.Aristotle.Physics.FirstCompletionTimeIndivisible
