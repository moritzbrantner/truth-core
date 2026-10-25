import TruthCore.Teleonomy.Mechanisms
namespace TruthCore.Results.Comparison.Teleonomy.ChanceIntentionDichotomy
open TruthCore.Teleonomy
open TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels

theorem chanceIntentionDichotomy : DichotomyFails := by
  have h := TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaActsForAnEnd.necessityModel
  exact ⟨fun _ _ h => h, h⟩
end TruthCore.Results.Comparison.Teleonomy.ChanceIntentionDichotomy
