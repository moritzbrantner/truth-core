import TruthCore.Causality.FiniteBranching

namespace TruthCore.Results.Causality.FiniteBranching

open TruthCore.Causality.FiniteBranching
open TruthCore.Case.Catholicism.StageOne.CausalFinitism

/-- Conditional causal bridge only; its mathematical premises do not establish
their own metaphysical applicability. -/
theorem checks {Entity : Type} (cause : Entity → Entity → Prop)
    (h0 : FiniteImmediatePredecessors cause)
    (h1 : WellFoundedPredecessors cause) :
    FiniteDistinctAncestry cause := by
  exact finiteAncestry_of_wellFounded_finiteImmediate cause h1 h0

end TruthCore.Results.Causality.FiniteBranching
