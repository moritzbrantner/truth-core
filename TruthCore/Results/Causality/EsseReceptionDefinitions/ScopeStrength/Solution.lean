module

public import TruthCore.Causality.EsseReceptionDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.EsseReceptionDefinitions.ScopeStrength
open TruthCore.Causality.EsseReception
open TruthCore.Causality.EsseReceptionDefinitionFork

/-- Frozen analyst obligation; no source communication is reinterpreted silently. -/
theorem scopeStrength (f : Frame)
    (h : EsseReceivedOnlyInOwnEssence f.essenceOf (f.Received f.selected)) :
    RestrictedOwnEssence f := by
  intro x r _ hr
  exact h x r hr

end TruthCore.Results.Causality.EsseReceptionDefinitions.ScopeStrength
