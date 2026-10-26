import TruthCore.Causality.RegressReadings

namespace TruthCore.Results.Causality.RegressAccessibilityExcludesSeries
open TruthCore.Causality

/-- Induction on the accessibility certificate of the series' last effect: a
series descending from an accessible `x` would yield, after dropping its first
member, a series descending from the accessible cause `series 1`. No classical
logic and no axiom is used. -/
theorem accessibilityReadingExcludesDescendingSeries :
    AccessibilityReadingExcludesDescendingSeries := by
  intro Being CausesAsCaused hAccessible ⟨series, hSeries⟩
  have noSeriesFrom : ∀ x, Acc CausesAsCaused x →
      ∀ s : Nat → Being, s 0 = x → DescendingPerSeSeries CausesAsCaused s → False := by
    intro x hAcc
    induction hAcc with
    | intro x _ ih =>
      intro s hStart hDesc
      exact ih (s 1) (hStart ▸ hDesc 0) (fun n => s (n + 1)) rfl (fun n => hDesc (n + 1))
  exact noSeriesFrom (series 0) (hAccessible (series 0)) series rfl hSeries

end TruthCore.Results.Causality.RegressAccessibilityExcludesSeries
