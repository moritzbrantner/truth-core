module

public import TruthCore.Results.Metaethics.GoodnessNamedElimination.Solution

@[expose] public section
namespace TruthCore.Results.Metaethics.GoodnessNamedCoverage
open TruthCore.Logic
open TruthCore.Metaethics.GoodnessFormEnd

/-- Reuses the checked named-scope coverage lemma. -/
theorem coverageOrFurtherDefinition (hEM : ExcludedMiddle) : NamedCoverageFork :=
  TruthCore.Results.Metaethics.GoodnessNamedElimination.namedCoverageFork hEM
end TruthCore.Results.Metaethics.GoodnessNamedCoverage
