module

public import TruthCore.Results.Causality.ComposerTemporalDefinitions.NoSelfStrength.Solution

@[expose] public section

namespace TruthCore.Results.Causality.ComposerTemporalDefinitions.NoSelfStrength.Bound

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting
open TruthCore.Causality.ComposerTemporalDefinitionFork
universe u v w

/-- Frozen analyst obligation; interpretation applicability remains open. -/
theorem noSelfStrength (f : Frame.{u,v,w}) (h : AllTimeNoSelf f) : NothingIsEfficientCauseOfItselfReading (Current f) := by
  exact TruthCore.Results.Causality.ComposerTemporalDefinitions.NoSelfStrength.noSelfStrength f h

end TruthCore.Results.Causality.ComposerTemporalDefinitions.NoSelfStrength.Bound
