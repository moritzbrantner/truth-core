import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3Interpretation
import TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels
namespace TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFacts.StrongReadingYields
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Results.Aquinas.SummaTheologiae

/-- In every motion model the strong-reading premises yield *a nullo movetur*:
the verified *prima via* theorem, instantiated at the model. No premises. -/
theorem strongReadingYieldsUnmovedMover : StrongReadingYieldsUnmovedMover :=
  PrimaViaModels.strongReadingYields

end TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFacts.StrongReadingYields
