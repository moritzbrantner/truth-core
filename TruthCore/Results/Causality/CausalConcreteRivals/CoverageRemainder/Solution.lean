module

public import TruthCore.Causality.CausalConcreteRivalBoundary

@[expose] public section
namespace TruthCore.Results.Causality.CausalConcreteRivals.CoverageRemainder
open TruthCore.Causality.CausalConcreteRivalBoundary
open TruthCore.Causality.CausalPowerConcreteness

/-- Analyst conditional obligation; original source readings and approved floor remain unchanged. -/
theorem coverageRemainder (f : Frame) (hEM : TruthCore.Logic.ExcludedMiddle) : CoverageFork f := by
  cases hEM (OtherCounter f) with
  | inl h => exact Or.inr h
  | inr hn =>
    left
    intro hc
    cases hEM (NamedCases f) with
    | inl h => exact h
    | inr h => exact False.elim (hn ⟨hc, h⟩)

end TruthCore.Results.Causality.CausalConcreteRivals.CoverageRemainder
