import TruthCore.Greek.Aristotle.Physics.BookI.Chapter2

namespace TruthCore.Results.Aristotle.Physics.ContinuousOneMany

open TruthCore.Greek.Aristotle.Physics

/--
If unity by continuity entails divisibility, and divisibility entails plurality in parts,
then unity by continuity entails plurality in parts.
-/
theorem continuousOneImpliesMany
    (OneByContinuity : Prop)
    (Divisible : Prop)
    (ManyInParts : Prop)
    (hDivisible : ContinuousOneImpliesDivisibleReading OneByContinuity Divisible)
    (hMany : DivisibleImpliesManyReading Divisible ManyInParts) :
    ContinuousOneImpliesManyReading OneByContinuity ManyInParts := by
  intro hContinuous
  exact hMany (hDivisible hContinuous)

end TruthCore.Results.Aristotle.Physics.ContinuousOneMany
