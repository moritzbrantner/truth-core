import TruthCore.Comparison.MoralError
namespace TruthCore.Results.Comparison.MoralError.EmotivismExcludesGenuineMoralContradiction
open TruthCore.English.OConnor
open TruthCore.Metaethics

/-- A genuine contradiction is about a sentence with a truth value. On emotivism
a moral sentence has none, so moral disagreement is never a contradiction. -/
theorem emotivismExcludesGenuineMoralContradiction {Agent Sentence : Type}
    (Accepts Rejects : Agent → Sentence → Prop) (Moral TruthApt : Sentence → Prop)
    (hEmotivism : MoralStatementsLackTruthValueReading Moral TruthApt) :
    NoGenuineMoralContradiction Accepts Rejects Moral TruthApt := by
  intro x y φ hMoral hContradict
  -- INF-CONTRADICTION-NEEDS-TRUTH-VALUE
  have hApt : TruthApt φ := hContradict.2.2
  -- INF-EMOTIVISM-EXCLUDES-GENUINE-MORAL-CONTRADICTION
  exact hEmotivism φ hMoral hApt

end TruthCore.Results.Comparison.MoralError.EmotivismExcludesGenuineMoralContradiction
