import TruthCore.Causality.NecessaryConcreteRootModels

namespace TruthCore.Results.Causality.NecessaryConcreteRoot.OmissionMatrix
open TruthCore.Causality.NecessaryConcreteRootModels

/-- Five finite certified controls: four single-premise deletions from the contradiction core and a concrete-predecessor typing counterexample. -/
theorem checks : OmissionMatrix := by
  exact omissionMatrix

end TruthCore.Results.Causality.NecessaryConcreteRoot.OmissionMatrix
