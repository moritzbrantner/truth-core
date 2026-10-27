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
  sorry

end TruthCore.Results.Case.Catholicism.StageThree.DivineFounding
