module

public import TruthCore.Causality.PossibleCauseOfContingency

@[expose] public section

namespace TruthCore.Results.Causality.ScenarioNecessaryWitness
open TruthCore.Causality.PossibleCauseOfContingency
open TruthCore.German.Kant.CosmologicalInference (NecessaryBeing)

theorem necessaryBearer {W B : Type} (s : Scenario W B) (w : W)
    (h : NecessaryConcreteAt s w) : NecessaryBeing s.ontic w := by
  obtain ⟨c, _, he, hn⟩ := h
  exact ⟨c, he, hn⟩

end TruthCore.Results.Causality.ScenarioNecessaryWitness
