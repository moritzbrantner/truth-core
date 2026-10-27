import TruthCore.Case.Catholicism.StageThree.DivineFounding

namespace TruthCore.Results.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding

/-- The skeleton's bridge `STMT-BRIDGE-CHRISTS-CHURCH-FOUNDED-BY-GOD` follows from
four typed premises: the resurrection is God's confirmation that Jesus holds
God's mandate; what God confirms is true; Jesus founded each visible
authoritative society he founded in the exercise of that mandate and
commissioned it to teach; and what Jesus so founds in a God's mandate, that God
founded as a teaching authority. The universal over societies is carried by the
scope premise. -/
theorem bridge_from_attested_mandate (σ : Signature) (A : Agency σ)
    (hAttest : ResurrectionConfirmsMandate σ A)
    (hVeracity : GodConfirmsOnlyTruth σ A)
    (hScope : MandatedFoundingWithTeaching σ A)
    (hEnvoy : EnvoyFoundingIsPrincipalsFounding σ A) :
    BridgeChristsChurchFoundedByGod σ := by
  intro g hGod hAttrs hReveals hClaimed hRose c hFounded hVisible
  -- Attestation and veracity: Jesus in fact holds a mandate from g.
  have hMandate : A.HoldsMandate σ.jesus g :=
    hVeracity g hGod hAttrs _ (hAttest g hGod hAttrs hReveals hClaimed hRose)
  -- Scope: this founding was done in that mandate, with a teaching commission.
  obtain ⟨hInMandate, hTeach⟩ := hScope g hMandate c hFounded hVisible
  -- Envoy founding: so g founded c as a teaching authority.
  exact hEnvoy g c hGod hInMandate hTeach

end TruthCore.Results.Case.Catholicism.StageThree.DivineFounding
