module

public import TruthCore.Logic.TemporalPastCoverage

@[expose] public section
namespace TruthCore.Results.Logic.TemporalPastCoverage.Coverage
open TruthCore.Logic.TemporalPastCoverage
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Exact logical coverage or source-bundle weakening; no philosophical branch is adopted. -/
theorem coverage {T : Type} (Before : T → T → Prop) (now : T)
    (hEM : TruthCore.Logic.ExcludedMiddle) : PastFork Before now := by
  cases hEM (PastIsFinite Before now) with
  | inl h => exact Or.inr h
  | inr hn =>
    left
    intro t ht
    cases hEM (∃ s, Before s t) with
    | inl h => exact h
    | inr h => exact False.elim (hn ⟨t, ht, fun s hs => h ⟨s, hs⟩⟩)

end TruthCore.Results.Logic.TemporalPastCoverage.Coverage
