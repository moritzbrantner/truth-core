module

public import TruthCore.Results.Causality.ComposerTemporalDefinitions.PastSelfCountermodel.Solution

@[expose] public section

namespace TruthCore.Results.Causality.ComposerTemporalDefinitions.PastSelfCountermodel.Bound
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting
open TruthCore.Causality.ComposerTemporalDefinitionFork

/-- The historical route fails under a selected-time-only self-causation ban,
 even with the same other three composition inputs and a nonempty composite. -/
theorem pastSelfCountermodel : PastSelfControl := by
  exact TruthCore.Results.Causality.ComposerTemporalDefinitions.PastSelfCountermodel.pastSelfCountermodel

end TruthCore.Results.Causality.ComposerTemporalDefinitions.PastSelfCountermodel.Bound
