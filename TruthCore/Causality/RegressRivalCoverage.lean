module

public import TruthCore.Results.Causality.RegressReadingsCoincide.Solution
public import TruthCore.Alternatives.ActPotencyRegress
public import TruthCore.Logic.ExcludedMiddle

/-! Reuse the existing Mathlib classical-choice coincidence theorem to expose
coverage behind the existing causal-regress rival. An infinite Nat-indexed
series need not have distinct members: loops are included. No real-world
causal interpretation, temporal past or truth of either branch follows. -/
@[expose] public section
namespace TruthCore.Causality.RegressRivalCoverage
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Alternatives.ActPotencyRegress

def RegressFork {B : Type} (R : B → B → Prop) : Prop :=
  NoInfinitePerSeEfficientCauseSeriesReading R ∨ InfinitePerSeCauseSeriesReading R
end TruthCore.Causality.RegressRivalCoverage
