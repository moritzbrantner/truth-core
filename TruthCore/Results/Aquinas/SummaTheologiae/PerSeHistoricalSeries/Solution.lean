module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.PerSeHistoricalSeries
public import TruthCore.Results.Causality.RegressAccessibilityExcludesSeries.Solution
public import TruthCore.Results.Causality.RegressAccessibilityUnboundedDepth.Solution
public import TruthCore.Results.Aquinas.SummaTheologiae.SecundaVia.Solution

@[expose] public section

namespace TruthCore.Results.Aquinas.SummaTheologiae.PerSeHistoricalSeries
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality

/-- Typed analyst distinction; no historical or metaphysical applicability claimed. -/
theorem distinction : PerSeHistoricalSeriesDistinction := by
  constructor
  · intro Being H E wf dictionary ⟨series, chain⟩
    exact TruthCore.Results.Causality.RegressAccessibilityExcludesSeries.accessibilityReadingExcludesDescendingSeries Being E wf
        ⟨series, fun n => dictionary _ _ (chain n)⟩
  · let E : Option Nat → Option Nat → Prop :=
      fun y x => y = none ∧ ∃ n, x = some n
    let H : Option Nat → Option Nat → Prop :=
      fun y x => ∃ n, y = some (n + 1) ∧ x = some n
    have root : Acc E none := by
      apply Acc.intro
      rintro y ⟨_, n, impossible⟩
      cases impossible
    refine ⟨E, H, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      apply Acc.intro
      rintro y ⟨hy, _⟩
      exact hy ▸ root
    · intro n
      exact ⟨rfl, n, rfl⟩
    · intro n
      exact ⟨n, rfl, rfl⟩
    · intro i j eq
      exact Option.some.inj eq
    · intro n
      exact ⟨n + 1, n, rfl, rfl⟩
    · rintro y x ⟨n, hy, _⟩ ⟨ey, _⟩
      have impossible := hy.symm.trans ey
      cases impossible

/-- Existing finite-depth control: unbounded finite depth is not infinite descent. -/
theorem finiteDepthControl : AccessibilityAllowsUnboundedDepth := by
  exact TruthCore.Results.Causality.RegressAccessibilityUnboundedDepth.accessibilityAllowsUnboundedDepth

/-- Rechecked existing omission controls, not independent new discoveries. -/
theorem secundaViaNeedsPerSeOrder :
    ¬ ∀ (Being Respect : Type)
      (E : Being → Being → Respect → Prop) (P C : Being → Being → Prop),
      OrderOfEfficientCausesFoundReading E →
      EfficientCauseIsPriorToEffectReading E P →
      NothingPriorToItselfReading P →
      NoInfinitePerSeEfficientCauseSeriesReading C →
      FirstEfficientCauseCannotBeLackingReading E := by
  exact TruthCore.Results.Aquinas.SummaTheologiae.SecundaVia.secundaViaNeedsPerSeOrder

theorem secundaViaNeedsNoRegress :
    ¬ ∀ (Being Respect : Type)
      (E : Being → Being → Respect → Prop) (P C : Being → Being → Prop),
      OrderOfEfficientCausesFoundReading E →
      EfficientCauseIsPriorToEffectReading E P →
      NothingPriorToItselfReading P →
      SecondEfficientCausesCauseOnlyAsCausedReading E C →
      FirstEfficientCauseCannotBeLackingReading E := by
  exact TruthCore.Results.Aquinas.SummaTheologiae.SecundaVia.secundaViaNeedsNoRegress

end TruthCore.Results.Aquinas.SummaTheologiae.PerSeHistoricalSeries
