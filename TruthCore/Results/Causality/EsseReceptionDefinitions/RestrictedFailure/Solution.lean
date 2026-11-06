module

public import TruthCore.Causality.EsseReceptionDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.EsseReceptionDefinitions.RestrictedFailure
open TruthCore.Causality.EsseReception
open TruthCore.Causality.EsseReceptionDefinitionFork

/-- Frozen analyst obligation; no source communication is reinterpreted silently. -/
theorem restrictedFailure (f : Frame) (hReception : SelectedReception f)
    (hDistinct : BodyIsNotSoulEssence f) (hEligible : SelectedSoulEligible f) :
    RestrictedOwnEssenceFails f := by
  intro h
  exact hDistinct (h (f.soulOf f.human) (f.bodyOf f.human) hEligible hReception)

end TruthCore.Results.Causality.EsseReceptionDefinitions.RestrictedFailure
