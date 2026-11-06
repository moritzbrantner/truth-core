module

public import TruthCore.Observation.ChangeRivalCoverage

@[expose] public section
namespace TruthCore.Results.Observation.ChangeRivalCoverage.BundleStrength
open TruthCore.Observation.ChangeRivalCoverage
open TruthCore.Observation.Change
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Alternatives.ActPotencyRegress

/-- Exact logical coverage or source-bundle weakening; no philosophical branch is adopted. -/
theorem bundleStrength {B : Type} (ASeries : B → Prop) (Opines : B → Prop → Prop) (Changes : B → Prop)
    (h : TruthCore.Comparison.McTaggart.UnrealityOfTime ASeries Opines Changes) : NoChange Changes := by
  intro x hx
  exact TruthCore.Results.Alternatives.McTaggartDefeatedByChange.bundleDefeatedByChange
    ASeries Opines Changes ⟨x, hx⟩ h

end TruthCore.Results.Observation.ChangeRivalCoverage.BundleStrength
