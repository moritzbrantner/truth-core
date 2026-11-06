module

public import TruthCore.Causality.EsseReceptionDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.EsseReceptionDefinitions.OwnEssenceFailure
open TruthCore.Causality.EsseReception
open TruthCore.Causality.EsseReceptionDefinitionFork

/-- Frozen analyst obligation; no source communication is reinterpreted silently. -/
theorem ownEssenceFailure (f : Frame) (hReception : SelectedReception f)
    (hDistinct : BodyIsNotSoulEssence f) : OwnEssenceFails f := by
  intro h
  exact hDistinct (h (f.soulOf f.human) (f.bodyOf f.human) hReception)

end TruthCore.Results.Causality.EsseReceptionDefinitions.OwnEssenceFailure
