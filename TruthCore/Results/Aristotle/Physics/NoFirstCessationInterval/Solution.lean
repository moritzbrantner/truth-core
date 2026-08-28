import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter8
namespace TruthCore.Results.Aristotle.Physics.NoFirstCessationInterval
open TruthCore.Greek.Aristotle.Physics
theorem noFirstCessationInterval (FirstCessationIntervalExists : Prop)
    (hSelfDefeating : ProposedFirstCessationIntervalNotFirstReading
      FirstCessationIntervalExists) :
    NoFirstCessationIntervalReading FirstCessationIntervalExists := by
  intro hFirst
  exact hSelfDefeating hFirst hFirst
end TruthCore.Results.Aristotle.Physics.NoFirstCessationInterval
