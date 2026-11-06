module

public import TruthCore.Case.Catholicism.StageThree.MessageReportBoundary
public import TruthCore.Case.Catholicism.StageThree.CommissionAttestation
public import TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary.Rival.Solution

@[expose] public section
namespace TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism.StageThree.Commissions
open TruthCore.Case.Catholicism.StageThree.CommissionAttestation
open TruthCore.Case.Catholicism.StageThree.MessageReportBoundary

theorem weakLinkAttestationRejectsMessage (σ : Signature) (A : Agency σ) (E : Commissioning) (T : Tradition)
    (hLink : GoverningEventInstitutionLink σ A E)
    (hIndep : JohnCommissionIndependent T)
    (hCrit : HeavenRatifiedAttestationCriterion E T) :
    MessageRivalExcludedGivenFounding σ A := by
  intro g hm hf hv hr
  obtain ⟨p, hp, hg⟩ := attestation_gives_governing E T hIndep hCrit
  have hn := messageOnlyRejectsGoverning σ A E hr hLink ⟨g, hm, hf, hv⟩
  exact hn p hp hg

end TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary
