module

public import TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Context

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

/-- The existing case's typed antecedents and attestation/scope supply a real
envoy-event witness; the definition of an event adds no holding premise. -/
theorem commissionedEventFromContext (σ : Signature) (A : Agency σ)
    (hGod : GodExists σ.IsGod)
    (hAttrs : GodHasClassicalAttributes σ)
    (hReveals : RevelationPossibleAndRecognizable σ)
    (hJesus : JesusClaimedDivineAuthorityAndRose σ)
    (hFounded : ChristFoundedVisibleChurch σ)
    (hAttest : ResurrectionConfirmsMandate σ A)
    (hVeracity : GodConfirmsOnlyTruth σ A)
    (hScope : MandatedFoundingWithTeaching σ A) :
    EnvoyEventExists σ A := by
  obtain ⟨g, hGodG⟩ := hGod
  obtain ⟨c, hFoundedC, hVisibleC⟩ := hFounded
  have hMandate : A.HoldsMandate σ.jesus g :=
    hVeracity g hGodG (hAttrs g hGodG) _
      (hAttest g hGodG (hAttrs g hGodG) (hReveals g hGodG) hJesus.1 hJesus.2)
  exact ⟨g, c, hGodG, hScope g hMandate c hFoundedC hVisibleC⟩

end TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Context
