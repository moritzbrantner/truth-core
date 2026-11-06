import TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

namespace TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Exclusive

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

/-- Frozen extra-condition comparison, not an identification with an author. -/
theorem exclusiveImmediateRejectsEnvoy (σ : Signature) (A : Agency σ) (direct : σ.Being → σ.Society → Prop)
    (hExclusive : ExclusiveImmediateReading σ A direct)
    (hEvent : EnvoyEventExists σ A) :
    EnvoyBridgeFails σ A := by
  sorry

end TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Exclusive
