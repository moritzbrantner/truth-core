import TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

namespace TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Strength

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

/-- Frozen extra-condition comparison, not an identification with an author. -/
theorem exclusiveImmediateWeakening (σ : Signature) (A : Agency σ) (direct : σ.Being → σ.Society → Prop)
    (hExclusive : ExclusiveImmediateReading σ A direct) :
    ImmediateOnlyReading σ A direct := by
  sorry

end TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Strength
