import TruthCore.Causality.WorldSourceRegress
namespace TruthCore.Results.Causality.WorldSourceRegress
open TruthCore.Causality.WorldSourceRegress
open TruthCore.German.Kant.CosmologicalInference
/-- Retain the path for each chosen node, strengthening the earlier
merely-some-source finite corollary. Only the existing acyclicity background
is assumed; finiteness and actual-node presence are explicit guards. -/
theorem finite_actual_all_sourcePaths {World Being : Type} (m : Ontic World Being)
    (hNoCycles : ActualAcyclic m) : FiniteActualAllSourcePaths m := by
  sorry
end TruthCore.Results.Causality.WorldSourceRegress
