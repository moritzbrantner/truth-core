import TruthCore.Causality.AtomisticCausalSource
import TruthCore.Logic.ExcludedMiddle

namespace TruthCore.Results.Causality.AtomisticCausalSource
open TruthCore.Logic.Regress (Graph)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Causality.AtomisticCausalSource

/-- Minimum source endpoint only, not effect-universality or necessity. -/
theorem source {B : Type} [PartialOrder B] (G : Graph B)
    (hPop : ObjectPopulation B) (hAtomic : AtomicParts B)
    (hCover : ConditionalCausedSimpleCover G) (hNoOverlap : CauseEffectNonoverlap G)
    (hEM : ExcludedMiddle) : SourceExists G := by
  sorry

/-- Activity gives the SAME selected source an outgoing effect. -/
theorem outgoing {B : Type} [PartialOrder B] (G : Graph B)
    (hPop : ObjectPopulation B) (hAtomic : AtomicParts B)
    (hCover : ConditionalCausedSimpleCover G) (hNoOverlap : CauseEffectNonoverlap G)
    (hEM : ExcludedMiddle) (hActivity : CausalActivity G) : OutgoingSourceExists G := by
  sorry

/-- Finite, nonvacuous consistency of the nonlogical interfaces and activity. -/
theorem consistency : Consistency := by
  sorry

end TruthCore.Results.Causality.AtomisticCausalSource
