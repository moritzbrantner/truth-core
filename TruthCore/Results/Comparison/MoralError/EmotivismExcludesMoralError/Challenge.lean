import TruthCore.Comparison.MoralError
namespace TruthCore.Results.Comparison.MoralError.EmotivismExcludesMoralError
open TruthCore.English.OConnor
open TruthCore.Metaethics
theorem emotivismExcludesMoralError {Agent Sentence : Type}
    (Accepts : Agent → Sentence → Prop) (Moral TruthApt Holds : Sentence → Prop)
    (hEmotivism : MoralStatementsLackTruthValueReading Moral TruthApt) :
    NoMoralError Accepts Moral TruthApt Holds := by
  sorry
end TruthCore.Results.Comparison.MoralError.EmotivismExcludesMoralError
