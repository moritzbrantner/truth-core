import TruthCore.Logic.Verificationism.NegationClosure
namespace TruthCore.Results.Logic.Verificationism.StrongVerificationClosure
open TruthCore.Logic.Verificationism
/-- Defeat 2 counted: with meaningfulness closed under negation for negated
sentences (the weak version), the V1 package fails. The negation of a testable law is conclusively verifiable, hence
meaningful; so its double negation is meaningful; but the double negation is
neither analytic (it fails where the counterinstance holds) nor conclusively
verifiable. -/
theorem strongVerificationismWithLawsFails {L : Language} (F : Frame L)
    (meaningful : L.Sentence → Prop) (hClosed : MeaningClosedUnderNegationOfNegations L meaningful) :
    StrongVerificationismWithLawsFails F meaningful := by
  sorry
end TruthCore.Results.Logic.Verificationism.StrongVerificationClosure
