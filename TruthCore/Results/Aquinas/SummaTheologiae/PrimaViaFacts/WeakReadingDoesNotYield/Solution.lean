import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3Interpretation
import TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels
namespace TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFacts.WeakReadingDoesNotYield
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Results.Aquinas.SummaTheologiae

/-- Countermodel: the finite `weakModel` satisfies every weaker-reading premise,
yet every being in it is moved in some respect. No premises. -/
theorem weakReadingDoesNotYieldUnmovedMover : WeakReadingDoesNotYieldUnmovedMover :=
  PrimaViaModels.weakReadingDoesNotYield

end TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFacts.WeakReadingDoesNotYield
