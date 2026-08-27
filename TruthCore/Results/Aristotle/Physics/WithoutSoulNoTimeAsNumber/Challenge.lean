import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter14

namespace TruthCore.Results.Aristotle.Physics.WithoutSoulNoTimeAsNumber

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's qualified soul/time argument in *Physics* IV.14, 223a21-29. -/
theorem withoutSoulNoTimeAsNumber
    (TimeExistsAsCountedOrCountableNumber CounterExists
      SoulOrIntellectInSoulExists : Prop)
    (hCounter :
      CountedOrCountableNumberRequiresCounterReading
        TimeExistsAsCountedOrCountableNumber CounterExists)
    (hSoul : OnlySoulIntellectCanCountReading CounterExists SoulOrIntellectInSoulExists) :
    WithoutSoulNoTimeAsNumberReading
      TimeExistsAsCountedOrCountableNumber SoulOrIntellectInSoulExists := by
  sorry

end TruthCore.Results.Aristotle.Physics.WithoutSoulNoTimeAsNumber
