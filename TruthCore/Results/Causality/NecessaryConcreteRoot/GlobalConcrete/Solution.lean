import TruthCore.Causality.NecessaryConcreteRoot

namespace TruthCore.Results.Causality.NecessaryConcreteRoot.GlobalConcrete
open TruthCore.Causality.NecessaryConcreteRoot

/-- All-world necessary concrete existence additionally needs the actual world's accessibility to cover every world; identity is rigid across the fixed roster. -/
theorem checks : GlobalConcreteRootConditional := by
  exact globalConcreteRootConditional

end TruthCore.Results.Causality.NecessaryConcreteRoot.GlobalConcrete
