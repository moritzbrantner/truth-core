module

public import TruthCore.Causality.EsseReceptionDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.EsseReceptionDefinitions.Counteraccount
open TruthCore.Causality.EsseReceptionDefinitionFork

/-- Exact counterexample elimination, not a philosophical global refutation. -/
theorem counteraccount (f : Frame) (h : FurtherInterpretation f) : SameSenseTransferFails f := by
  intro ht
  obtain ⟨s, h, e, hu, hc, he, hn⟩ := h
  exact hn (ht s h e hu hc he)

end TruthCore.Results.Causality.EsseReceptionDefinitions.Counteraccount
