import TruthCore.Causality.AtomisticCausalSource
import TruthCore.Causality.SourceWitness

/-! Mechanical interfaces only: preserve existing statement identities and the
SAME graph, carrier and edge interpretation. No new causal, modal, grounding,
well-foundedness or philosophical assumption is introduced or established. -/
namespace TruthCore.Results.Causality.SourceForestInterop
open TruthCore.Logic.Regress (Graph)
open TruthCore.Causality.AtomisticCausalSource
open TruthCore.Causality.SourceWitness (HasSource)
open TruthCore.Causality.SourceForest (UniquePredecessor)

/-- Assembly: the same graph-relative source existential is repackaged. -/
theorem hasSource {B : Type} (G : Graph B) (h : SourceExists G) : HasSource G := by
  sorry

/-- Assembly: unique incoming cause per effect differs only in binder order.
This does NOT assert at-most-one graph source or one effect per producer. -/
theorem uniquePredecessor {B : Type} (G : Graph B) (h : UniqueCausePerEffect G) :
    UniquePredecessor G := by
  sorry

end TruthCore.Results.Causality.SourceForestInterop
