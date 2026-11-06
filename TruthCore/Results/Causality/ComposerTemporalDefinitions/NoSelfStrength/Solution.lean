module

public import TruthCore.Causality.ComposerTemporalDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.ComposerTemporalDefinitions.NoSelfStrength

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting
open TruthCore.Causality.ComposerTemporalDefinitionFork
universe u v w

/-- Frozen analyst obligation; interpretation applicability remains open. -/
theorem noSelfStrength (f : Frame.{u,v,w}) (h : AllTimeNoSelf f) : CurrentNoSelf f := by
  exact h f.now

end TruthCore.Results.Causality.ComposerTemporalDefinitions.NoSelfStrength
