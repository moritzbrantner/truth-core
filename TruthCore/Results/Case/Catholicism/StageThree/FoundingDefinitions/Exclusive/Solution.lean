module

public import TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Exclusive

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

/-- Frozen extra-condition comparison, not an identification with an author. -/
theorem exclusiveImmediateRejectsEnvoy (σ : Signature) (A : Agency σ) (direct : σ.Being → σ.Society → Prop)
    (hExclusive : ExclusiveImmediateReading σ A direct)
    (hEvent : EnvoyEventExists σ A) :
    EnvoyBridgeFails σ A := by
  intro hEnvoy
  obtain ⟨g, c, hGod, hFounded, hTeach⟩ := hEvent
  have hTarget := hEnvoy g c hGod hFounded hTeach
  have hDirect := (hExclusive.1 g c hGod).1 hTarget
  exact hExclusive.2 g c hGod ⟨hFounded, hTeach⟩ hDirect

end TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Exclusive
