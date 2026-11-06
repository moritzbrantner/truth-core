module

public import TruthCore.Results.Causality.CausalConcreteRivals.StructuralCoverage.Solution

@[expose] public section
namespace TruthCore.Results.Causality.CausalConcreteRivals.NamedElimination
open TruthCore.Causality.CausalConcreteRivalBoundary
open TruthCore.Causality.CausalPowerConcreteness

/-- Analyst conditional obligation; original source readings and approved floor remain unchanged. -/
theorem namedElimination (f : Frame) (hEM : TruthCore.Logic.ExcludedMiddle)
    (hCal : Calibration f) (hCover : NamedCoverage f) (hFail : NamedCasesFail f) :
    OwnerCommitmentAt f.ontic f.concrete f.power f.selected := by
  cases TruthCore.Results.Causality.CausalConcreteRivals.StructuralCoverage.structuralCoverage f hEM hCal with
  | inl h => exact h
  | inr h =>
    rcases hCover h with hs | hf | hm
    · exact False.elim (hFail.1 hs)
    · exact False.elim (hFail.2.1 hf)
    · exact False.elim (hFail.2.2 hm)

end TruthCore.Results.Causality.CausalConcreteRivals.NamedElimination
