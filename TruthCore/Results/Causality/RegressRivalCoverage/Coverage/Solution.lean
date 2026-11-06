module

public import TruthCore.Causality.RegressRivalCoverage

@[expose] public section
namespace TruthCore.Results.Causality.RegressRivalCoverage.Coverage
open TruthCore.Causality.RegressRivalCoverage
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Alternatives.ActPotencyRegress

/-- Exact logical coverage or source-bundle weakening; no philosophical branch is adopted. -/
theorem coverage {B : Type} (R : B → B → Prop) (hEM : TruthCore.Logic.ExcludedMiddle) : RegressFork R := by
  cases hEM (InfinitePerSeCauseSeriesReading R) with
  | inl h => exact Or.inr h
  | inr h =>
    left
    exact (TruthCore.Results.Causality.RegressReadingsCoincide.regressReadingsCoincideClassically B R).mpr h

end TruthCore.Results.Causality.RegressRivalCoverage.Coverage
