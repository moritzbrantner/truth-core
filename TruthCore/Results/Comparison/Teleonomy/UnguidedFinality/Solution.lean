module

public import TruthCore.Teleonomy.Mechanisms

@[expose] public section

namespace TruthCore.Results.Comparison.Teleonomy.UnguidedFinality
open TruthCore.Teleonomy
open TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels

theorem unguidedFinality : UnguidedFinalityModel := by
  exact TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaEachDirected.teleonomyModel
end TruthCore.Results.Comparison.Teleonomy.UnguidedFinality
