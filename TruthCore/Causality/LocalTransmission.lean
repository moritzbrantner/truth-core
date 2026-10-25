import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia

namespace TruthCore.Causality
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Bare local dependence is a different constraint: each intermediate
being's activity agrees with that of its predecessor. It does not say that
activity must be initiated at a first link. -/
def LocalTransmission (active : Nat → Prop) : Prop :=
  ∀ n, active n ↔ active (n + 1)

/-- A value at one endpoint selects the global solution of these local
equations, even though there is no first upstream cause. This alone does
not explain why the observed endpoint has its activity. -/
def LocalObservationSelectsSolution : Prop :=
  ∀ active : Nat → Prop, LocalTransmission active →
    (active 0 → ∀ n, active n) ∧
    (¬ active 0 → ∀ n, ¬ active n)

/-- A countermodel to the inference from a successor ordering and local
transmission to causal well-foundedness. It does not assign metaphysical
derivative causal power to the links in the model. -/
def InfiniteLocalTransmissionModel : Prop :=
  ∃ (causesAsCaused : Nat → Nat → Prop) (active : Nat → Prop),
    (∀ n, causesAsCaused (n + 1) n) ∧
    LocalTransmission active ∧ active 0 ∧
    ¬ NoInfinitePerSeEfficientCauseSeriesReading causesAsCaused

/-- A reusable purely mathematical counterexample: the predecessor of `n`
is `n + 1`, so no node has a finite accessibility derivation. -/
theorem successorChainNotWellFounded :
    ¬ NoInfinitePerSeEfficientCauseSeriesReading
      (fun (y x : Nat) => y = x + 1) := by
  intro hWellFounded
  have notAcc : ∀ n, ¬ Acc (fun (y x : Nat) => y = x + 1) n := by
    intro n hAcc
    induction hAcc with
    | intro x _ ih => exact ih (x + 1) rfl
  exact notAcc 0 (hWellFounded 0)

end TruthCore.Causality
