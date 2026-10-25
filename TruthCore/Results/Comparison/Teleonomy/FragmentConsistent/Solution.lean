import TruthCore.Comparison.Teleonomy
import TruthCore.Results.Comparison.Teleonomy.SelectionCoverage.Solution
import TruthCore.Results.Comparison.Teleonomy.FeedbackCoverage.Solution
import TruthCore.Results.Comparison.Teleonomy.UnguidedFinality.Solution
namespace TruthCore.Results.Comparison.Teleonomy.FragmentConsistent
open TruthCore.Comparison.Teleonomy
/-- Satisfiability of the concrete fragment, not truth of global naturalism. -/
theorem fragmentConsistent : NaturalisticFragment := by
  exact ⟨SelectionCoverage.selectionCoverage, FeedbackCoverage.feedbackCoverage,
    UnguidedFinality.unguidedFinality⟩
end TruthCore.Results.Comparison.Teleonomy.FragmentConsistent
