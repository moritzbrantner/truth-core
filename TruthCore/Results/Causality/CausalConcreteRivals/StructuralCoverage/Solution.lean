module

public import TruthCore.Causality.CausalConcreteRivalBoundary

@[expose] public section
namespace TruthCore.Results.Causality.CausalConcreteRivals.StructuralCoverage
open TruthCore.Causality.CausalConcreteRivalBoundary
open TruthCore.Causality.CausalPowerConcreteness

/-- Analyst conditional obligation; original source readings and approved floor remain unchanged. -/
theorem structuralCoverage (f : Frame) (hEM : TruthCore.Logic.ExcludedMiddle)
    (hCal : Calibration f) : StructuralFork f := by
  cases hEM (SelectedCounter f) with
  | inl h => exact Or.inr h
  | inr hn =>
    left
    constructor
    · intro x hp
      cases hEM (Esse f x) with
      | inl hx => exact (hCal x).mpr hx
      | inr hx => exact False.elim (hn ⟨x, hx, Or.inl hp⟩)
    · intro x y hc
      cases hEM (Esse f x) with
      | inl hx => exact (hCal x).mpr hx
      | inr hx => exact False.elim (hn ⟨x, hx, Or.inr ⟨y, hc⟩⟩)

end TruthCore.Results.Causality.CausalConcreteRivals.StructuralCoverage
