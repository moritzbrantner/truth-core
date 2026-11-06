module

public import TruthCore.Causality.ComposerTemporalDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.ComposerTemporalDefinitions.Calibration

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting
open TruthCore.Causality.ComposerTemporalDefinitionFork
universe u v w

/-- Frozen analyst obligation; interpretation applicability remains open. -/
theorem calibration (f : Frame.{u,v,w}) (hDef : TemporalDefinition f)
    (hComposer : AttributedComposer f) : TemporalComposer f := by
  intro c a b x hu
  obtain ⟨r, hr⟩ := hComposer c a b x hu
  exact ⟨r, (hDef c x r).mp hr⟩

end TruthCore.Results.Causality.ComposerTemporalDefinitions.Calibration
