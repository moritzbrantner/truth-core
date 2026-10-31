import TruthCore.Case.Catholicism.StageThree.CommissionAttestation

namespace TruthCore.Results.Case.Catholicism.StageThree.CommissionAttestation
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism.StageThree.Commissions
open TruthCore.Case.Catholicism.StageThree.CommissionAttestation

/-- The message rival is excluded by multiple attestation, given the founding:
if the link premise `STMT-CHURCH-FOUNDED-IN-COMMISSIONED-APOSTLES` holds, John
20.21-23's commission saying is independent of Matthew 18.17-18's or of Matthew
16.18-19's, and the criterion of multiple attestation holds for the
heaven-ratified family (binding and loosing, forgiving and retaining), then for
any `g` from which Jesus holds a mandate, if he founded the Catholic Church as a
visible society with authority, the message rival `MandateCoversOnlyMessage`
is false. The step from the premises runs through the reported content: the
family is reported in both strands and every power in it is governing. -/
theorem message_rival_excluded_by_attestation (σ : Signature) (A : Agency σ)
    (E : Commissioning) (T : Tradition)
    (hLink : ChurchFoundedInCommissionedApostles σ A E)
    (hIndep : JohnCommissionIndependent T)
    (hCrit : HeavenRatifiedAttestationCriterion E T) :
    MessageRivalExcludedGivenFounding σ A := by
  sorry

end TruthCore.Results.Case.Catholicism.StageThree.CommissionAttestation
