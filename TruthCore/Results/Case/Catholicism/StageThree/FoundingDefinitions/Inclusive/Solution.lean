module

public import TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Inclusive

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

/-- Frozen semantic-comparison obligation; no preferred reading is adopted. -/
theorem inclusiveSuppliesEnvoy (σ : Signature) (A : Agency σ) (direct : σ.Being → σ.Society → Prop)
    (hInclusive : EnvoyInclusiveReading σ A direct) :
    EnvoyFoundingIsPrincipalsFounding σ A := by
  intro g c hGod hFounded hTeach
  exact (hInclusive g c hGod).2 (Or.inr ⟨hFounded, hTeach⟩)

end TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Inclusive
