import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter5
namespace TruthCore.Results.Aristotle.Physics.NoFirstChangingTime
open TruthCore.Greek.Aristotle.Physics
theorem noFirstChangingTime (FirstChangingTimeExists : Prop)
    (hSelfRefuting : ProposedFirstChangingTimeNotFirstReading FirstChangingTimeExists) :
    NoFirstChangingTimeReading FirstChangingTimeExists := by
  intro hFirst
  exact hSelfRefuting hFirst hFirst
end TruthCore.Results.Aristotle.Physics.NoFirstChangingTime
