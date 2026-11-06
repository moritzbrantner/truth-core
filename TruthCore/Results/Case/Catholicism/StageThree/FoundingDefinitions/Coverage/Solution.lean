module

public import TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Coverage

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

/-- Frozen semantic-comparison obligation; no preferred reading is adopted. -/
theorem readingCoverage (σ : Signature) (A : Agency σ) (direct : σ.Being → σ.Society → Prop)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    ReadingCoverageWithRemainder σ A direct := by
  cases hEM (ImmediateOnlyReading σ A direct) with
  | inl h => exact Or.inl h
  | inr hNotImmediate =>
    cases hEM (EnvoyInclusiveReading σ A direct) with
    | inl h => exact Or.inr (Or.inl h)
    | inr hNotInclusive => exact Or.inr (Or.inr ⟨hNotImmediate, hNotInclusive⟩)

end TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Coverage
