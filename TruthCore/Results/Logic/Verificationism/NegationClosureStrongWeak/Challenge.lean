import TruthCore.Logic.Verificationism.NegationClosure
namespace TruthCore.Results.Logic.Verificationism.NegationClosureStrongWeak
open TruthCore.Logic.Verificationism
/-- The strong version of negation closure entails the weak one: closure for
every sentence gives it in particular for negated sentences. -/
theorem negationClosureStrongEntailsWeak {L : Language} (meaningful : L.Sentence → Prop)
    (hStrong : MeaningClosedUnderNegation L meaningful) :
    MeaningClosedUnderNegationOfNegations L meaningful := by
  sorry
end TruthCore.Results.Logic.Verificationism.NegationClosureStrongWeak
