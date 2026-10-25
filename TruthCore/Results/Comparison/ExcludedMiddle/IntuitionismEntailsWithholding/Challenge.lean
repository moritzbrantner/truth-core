import TruthCore.Comparison.ExcludedMiddle
namespace TruthCore.Results.Comparison.ExcludedMiddle.IntuitionismEntailsWithholding
open TruthCore.Logic
open TruthCore.Comparison.ExcludedMiddle
/-- The intuitionist theory entails withholding excluded middle, and not
denying it: asserting `p ∨ ¬p` needs a proof of `p` or of `¬p`; an undecided
proposition's instance is therefore not asserted; and every denial of an
instance stays refuted. The withholding is derived from the theory's account of
truth and assertion, not stipulated. -/
theorem intuitionismEntailsExcludedMiddleWithheld (s : Sig) (hTheory : Intuitionist s)
    (hAssertion : TruthCore.English.Iemhoff.AssertionRequiresProofReading s.Proved s.Asserts) :
    ExcludedMiddleWithheld s.Proved s.Asserts := by
  sorry
end TruthCore.Results.Comparison.ExcludedMiddle.IntuitionismEntailsWithholding
