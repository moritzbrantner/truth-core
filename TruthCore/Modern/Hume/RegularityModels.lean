import TruthCore.Comparison.HumeRegularity

namespace TruthCore.Modern.Hume.Regularity
open TruthCore.Comparison.HumeRegularity

/-- Each selected thin theory has a model. This does not make its answers
correct about our cosmos, nor make observational sufficiency true. -/
def ModelChecks : Prop :=
  (∃ m, BareObservational m) ∧ (∃ m, InterventionEnriched m) ∧ (∃ s, ScopedBrute s)

end TruthCore.Modern.Hume.Regularity
