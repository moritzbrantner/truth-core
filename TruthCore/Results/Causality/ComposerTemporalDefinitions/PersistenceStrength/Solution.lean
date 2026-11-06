module

public import TruthCore.Causality.ComposerTemporalDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.ComposerTemporalDefinitions.PersistenceStrength

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting
open TruthCore.Causality.ComposerTemporalDefinitionFork
universe u v w

/-- Frozen analyst obligation; interpretation applicability remains open. -/
theorem persistenceStrength (f : Frame.{u,v,w}) (h : GlobalPersistence f) : UniterPersistence f := by
  intro c a b x _ hh
  obtain ⟨r, hr⟩ := hh
  exact ⟨r, h c x r hr⟩

end TruthCore.Results.Causality.ComposerTemporalDefinitions.PersistenceStrength
