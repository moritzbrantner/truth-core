import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3Interpretation
import TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels
namespace TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFacts.ObjectionExposesWeakGap
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Results.Aquinas.SummaTheologiae

/-- Model: the finite `weakModel` satisfies the weaker-reading premises and the
irrelevant-respect objection, and no being in it is moved by none. No premises. -/
theorem irrelevantRespectObjectionExposesWeakGap : IrrelevantRespectObjectionExposesWeakGap :=
  ⟨PrimaViaModels.weakModel, PrimaViaModels.weakModel_premises,
    PrimaViaModels.weakModel_objection, PrimaViaModels.weakModel_no_unmoved_mover⟩

end TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFacts.ObjectionExposesWeakGap
