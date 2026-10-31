import TruthCore.Causality.PossibleCauseOfContingency

namespace TruthCore.Results.Causality.ScenarioNecessaryWitness
open TruthCore.Causality.PossibleCauseOfContingency
open TruthCore.German.Kant.CosmologicalInference (NecessaryBeing)

theorem necessaryBearer {W B : Type} (s : Scenario W B) (w : W)
    (h : NecessaryConcreteAt s w) : NecessaryBeing s.ontic w := by
  sorry

end TruthCore.Results.Causality.ScenarioNecessaryWitness
