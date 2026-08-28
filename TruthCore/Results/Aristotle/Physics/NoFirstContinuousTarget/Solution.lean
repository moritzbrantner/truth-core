import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter5
namespace TruthCore.Results.Aristotle.Physics.NoFirstContinuousTarget
open TruthCore.Greek.Aristotle.Physics
theorem noFirstContinuousTarget
    (FirstTargetIndivisible FirstTargetDivisible FirstContinuousTargetExists : Prop)
    (hCases : FirstContinuousTargetDivisibleOrIndivisibleReading
      FirstTargetIndivisible FirstTargetDivisible)
    (hExcludes : EitherTargetCaseExcludesFirstReading FirstTargetIndivisible
      FirstTargetDivisible FirstContinuousTargetExists) :
    NoFirstContinuousTargetReading FirstContinuousTargetExists := by
  rcases hCases with hIndivisible | hDivisible
  · exact hExcludes.1 hIndivisible
  · exact hExcludes.2 hDivisible
end TruthCore.Results.Aristotle.Physics.NoFirstContinuousTarget
