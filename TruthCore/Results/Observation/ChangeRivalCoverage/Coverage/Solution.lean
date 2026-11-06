module

public import TruthCore.Observation.ChangeRivalCoverage

@[expose] public section
namespace TruthCore.Results.Observation.ChangeRivalCoverage.Coverage
open TruthCore.Observation.ChangeRivalCoverage
open TruthCore.Observation.Change
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Alternatives.ActPotencyRegress

/-- Exact logical coverage or source-bundle weakening; no philosophical branch is adopted. -/
theorem coverage {B : Type} (Changes : B → Prop) (hEM : TruthCore.Logic.ExcludedMiddle) : ChangeFork Changes := by
  cases hEM (SomethingChangesReading Changes) with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr (fun x hx => h ⟨x, hx⟩)

end TruthCore.Results.Observation.ChangeRivalCoverage.Coverage
