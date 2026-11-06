module

public import TruthCore.Causality.EsseReceptionDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.EsseReceptionDefinitions.TransferCoverage
open TruthCore.Causality.EsseReception
open TruthCore.Causality.EsseReceptionDefinitionFork

/-- Frozen analyst obligation; no source communication is reinterpreted silently. -/
theorem transferCoverage (hEM : TruthCore.Logic.ExcludedMiddle) : TransferFork := by
  intro f
  cases hEM (FurtherInterpretation f) with
  | inl h => exact Or.inr h
  | inr hn =>
    apply Or.inl
    intro s h e hu hc he
    cases hEM (f.Received s (f.soulOf h) (f.bodyOf h)) with
    | inl hr => exact hr
    | inr hr => exact False.elim (hn ⟨s, h, e, hu, hc, he, hr⟩)

end TruthCore.Results.Causality.EsseReceptionDefinitions.TransferCoverage
