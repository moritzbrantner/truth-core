module

public import TruthCore.Observation.ChangeRivalCoverage

@[expose] public section
namespace TruthCore.Results.Observation.ChangeRivalCoverage.CounterFailure
open TruthCore.Observation.ChangeRivalCoverage
open TruthCore.Observation.Change
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Alternatives.ActPotencyRegress

/-- Exact logical coverage or source-bundle weakening; no philosophical branch is adopted. -/
theorem counterFailure {B : Type} (Changes : B → Prop) (h : NoChange Changes) : ChangeFails Changes := by
  exact fun ⟨x, hx⟩ => h x hx

end TruthCore.Results.Observation.ChangeRivalCoverage.CounterFailure
