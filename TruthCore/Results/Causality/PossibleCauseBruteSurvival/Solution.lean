import TruthCore.Causality.PossibleCauseOfContingency

namespace TruthCore.Results.Causality.PossibleCauseBruteSurvival

open TruthCore.Causality.PossibleCauseOfContingency

/-- Source-free modal scope diagnostic only, under the exact stipulated
concreteness, transworld-identity and causation semantics of the imported
Scenario. No metaphysical possibility or actual-world causal principle is
established by this theorem. -/
theorem checks : CausalOpportunityBruteRootCompatibility := by
  exact causalOpportunityDoesNotExcludeBruteRoots

end TruthCore.Results.Causality.PossibleCauseBruteSurvival
