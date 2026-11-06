module

public import TruthCore.Causality.EsseReceptionDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.EsseReceptionDefinitions.SelectedCoverage
open TruthCore.Causality.EsseReception
open TruthCore.Causality.EsseReceptionDefinitionFork

/-- Frozen analyst obligation; no source communication is reinterpreted silently. -/
theorem selectedCoverage (hEM : TruthCore.Logic.ExcludedMiddle) : SelectedFork := by
  intro f
  exact hEM (SelectedReception f)

end TruthCore.Results.Causality.EsseReceptionDefinitions.SelectedCoverage
