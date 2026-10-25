import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3Interpretation
import TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels
namespace TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFacts.StrongPremisesCompatibleWithObjection
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Results.Aquinas.SummaTheologiae

/-- Model: the finite `strongModel` satisfies every strong-reading premise and the
irrelevant-respect objection's situation. No premises. -/
theorem strongPremisesCompatibleWithIrrelevantRespectObjection : StrongPremisesCompatibleWithIrrelevantRespectObjection :=
  ⟨PrimaViaModels.strongModel, PrimaViaModels.strongModel_premises,
    PrimaViaModels.strongModel_objection⟩

end TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFacts.StrongPremisesCompatibleWithObjection
