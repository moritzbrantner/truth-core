import TruthCore.Comparison.MoralError
namespace TruthCore.Results.Comparison.MoralError.EmotivismExcludesGenuineMoralContradiction
open TruthCore.English.OConnor
open TruthCore.Metaethics
theorem emotivismExcludesGenuineMoralContradiction {Agent Sentence : Type}
    (Accepts Rejects : Agent → Sentence → Prop) (Moral TruthApt : Sentence → Prop)
    (hEmotivism : MoralStatementsLackTruthValueReading Moral TruthApt) :
    NoGenuineMoralContradiction Accepts Rejects Moral TruthApt := by
  sorry
end TruthCore.Results.Comparison.MoralError.EmotivismExcludesGenuineMoralContradiction
