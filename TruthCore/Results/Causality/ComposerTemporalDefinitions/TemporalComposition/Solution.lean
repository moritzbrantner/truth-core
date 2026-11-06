module

public import TruthCore.Causality.ComposerTemporalDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.ComposerTemporalDefinitions.TemporalComposition

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting
open TruthCore.Causality.ComposerTemporalDefinitionFork
universe u v w

/-- Frozen analyst obligation; interpretation applicability remains open. -/
theorem temporalComposition (f : Frame.{u,v,w}) (Composite : f.Being → Prop)
    (ComponentOf : f.Being → f.Being → Prop)
    (CausesIn : f.Being → f.Being → f.Respect → Prop) (esse : f.Respect)
    (hTwo : CompositeHasTwoDistinctComponentsReading Composite ComponentOf)
    (hUnite : DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf f.Unites)
    (hComposer : TemporalComposer f)
    (hBeing : UnitingCauseCausesBeingReading f.Unites CausesIn esse)
    (hNoSelf : AllTimeNoSelf f) : CompositeConclusion f Composite CausesIn esse := by
  apply TruthCore.Results.Aquinas.SummaTheologiae.CompositeUnitingCauseFromUnion.compositeHasAUnitingCause
    Composite ComponentOf f.Unites (Temporal f) CausesIn esse hTwo hUnite hComposer hBeing
  intro x r hx
  obtain ⟨t, ht⟩ := hx
  exact hNoSelf t x r ht

end TruthCore.Results.Causality.ComposerTemporalDefinitions.TemporalComposition
