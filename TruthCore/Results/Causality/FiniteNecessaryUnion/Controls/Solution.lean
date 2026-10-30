import TruthCore.Causality.FiniteNecessaryUnion

namespace TruthCore.Results.Causality.FiniteNecessaryUnion.Controls

open TruthCore.Causality.FiniteNecessaryUnion
open TruthCore.German.Kant.CosmologicalInference

/-- Joint controls on explicit finite interpretations: source plus independent two-cycle; rotating local acyclicity with no union source and a union cycle; benign varying source without a union cycle despite a novel necessary edge. Reuses the unchanged rotating and varying model theorems. These refute exclusivity of source/cycle and any inference from variable edges alone to absence of a common source; no metaphysical interpretation is established. -/
theorem checks : ModelControls := by
  exact model_controls

end TruthCore.Results.Causality.FiniteNecessaryUnion.Controls
