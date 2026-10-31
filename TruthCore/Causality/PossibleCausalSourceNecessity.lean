import TruthCore.Causality.HeadlessCausalAncestry
import TruthCore.Causality.NecessarilyUnderived

/-! Source-free same-individual modal composition. The possible opportunity
concerns branching full ancestor cones of the existing actual causal graph.
It is not attributed to the survey, and says nothing about concrete/capable
candidate domains. No causation-grounding identification or new ontology. -/
namespace TruthCore.Causality.PossibleCausalSourceNecessity
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Causality.HeadlessCausalAncestry

/-- OPEN opportunity: an accessible world fails universal headless-full-cone
coverage. Empty actual domains cannot witness this failure. No temporal first
moment, unique source or exclusion of every infinite branch is asserted. -/
def PossiblyFailedHeadlessCoverage {W B : Type} (m : Ontic W B) (w : W) : Prop :=
  ∃ v, m.frame.access w v ∧
    ¬ ∀ selected : Actual m v, HeadlessFullAncestry (actualGraph m v) selected

end TruthCore.Causality.PossibleCausalSourceNecessity
