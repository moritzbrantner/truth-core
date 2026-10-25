import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia

namespace TruthCore.Causality
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Bare local dependence is a different constraint: each intermediate
being's activity agrees with that of its predecessor. It does not say that
activity must be initiated at a first link. -/
def LocalTransmission (active : Nat → Prop) : Prop :=
  ∀ n, active n ↔ active (n + 1)

/-- A countermodel to the inference from a successor ordering and local
transmission to causal well-foundedness. It does not assign metaphysical
derivative causal power to the links in the model. -/
def InfiniteLocalTransmissionModel : Prop :=
  ∃ (causesAsCaused : Nat → Nat → Prop) (active : Nat → Prop),
    (∀ n, causesAsCaused (n + 1) n) ∧
    LocalTransmission active ∧ active 0 ∧
    ¬ NoInfinitePerSeEfficientCauseSeriesReading causesAsCaused

end TruthCore.Causality
