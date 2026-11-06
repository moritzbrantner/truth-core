module

public import TruthCore.Causality.ComposerTemporalDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.ComposerTemporalDefinitions.CurrentTransfer

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting
open TruthCore.Causality.ComposerTemporalDefinitionFork
universe u v w

/-- Frozen analyst obligation; interpretation applicability remains open. -/
theorem currentTransfer (f : Frame.{u,v,w}) (hComposer : TemporalComposer f)
    (hPersistence : UniterPersistence f) : CurrentComposer f := by
  intro c a b x hu
  exact hPersistence c a b x hu (hComposer c a b x hu)

end TruthCore.Results.Causality.ComposerTemporalDefinitions.CurrentTransfer
