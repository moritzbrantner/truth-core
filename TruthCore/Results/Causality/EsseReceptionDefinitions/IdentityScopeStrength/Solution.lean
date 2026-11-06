module

public import TruthCore.Causality.EsseReceptionDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.EsseReceptionDefinitions.IdentityScopeStrength
open TruthCore.Causality.EsseReception
open TruthCore.Causality.EsseReceptionDefinitionFork
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception

/-- Frozen exact scope obligation; source claims and original Challenges remain unchanged. -/
theorem identityScopeStrength (f : Frame)
    (h : EsseReceivedOnlyInOwnEssence f.essenceOf (f.Received f.selected)) :
    IdentityScopedOwnEssence f := by
  intro x r _ hr
  exact h x r hr

end TruthCore.Results.Causality.EsseReceptionDefinitions.IdentityScopeStrength
