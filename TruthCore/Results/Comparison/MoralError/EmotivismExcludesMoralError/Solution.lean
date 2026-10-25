import TruthCore.Comparison.MoralError
namespace TruthCore.Results.Comparison.MoralError.EmotivismExcludesMoralError
open TruthCore.English.OConnor
open TruthCore.Metaethics

/-- To err about a moral sentence is to accept it while it has a truth value
and is not true. On emotivism it has no truth value. -/
theorem emotivismExcludesMoralError {Agent Sentence : Type}
    (Accepts : Agent → Sentence → Prop) (Moral TruthApt Holds : Sentence → Prop)
    (hEmotivism : MoralStatementsLackTruthValueReading Moral TruthApt) :
    NoMoralError Accepts Moral TruthApt Holds := by
  intro x φ hMoral hErrs
  -- INF-ERROR-NEEDS-TRUTH-VALUE: an error is about a sentence with a truth value
  have hApt : TruthApt φ := hErrs.2.1
  -- INF-EMOTIVISM-EXCLUDES-MORAL-ERROR: emotivism denies the moral sentence one
  exact hEmotivism φ hMoral hApt

end TruthCore.Results.Comparison.MoralError.EmotivismExcludesMoralError
