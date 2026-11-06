module

public import TruthCore.Case.Catholicism.StageThree.FoundingDefinitions
public import TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Inclusive.Solution

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Elimination

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

/-- Frozen semantic-comparison obligation; no preferred reading is adopted. -/
theorem namedElimination (σ : Signature) (A : Agency σ) (direct : σ.Being → σ.Society → Prop)
    (hCoverage : NamedReadingCoverage σ A direct)
    (hNotImmediate : ImmediateReadingFails σ A direct) :
    EnvoyFoundingIsPrincipalsFounding σ A := by
  cases hCoverage with
  | inl hImmediate => exact False.elim (hNotImmediate hImmediate)
  | inr hInclusive =>
    exact TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Inclusive.inclusiveSuppliesEnvoy
      σ A direct hInclusive

end TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Elimination
