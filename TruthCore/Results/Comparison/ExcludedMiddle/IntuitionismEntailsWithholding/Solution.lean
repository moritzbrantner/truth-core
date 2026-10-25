import TruthCore.Comparison.ExcludedMiddle
namespace TruthCore.Results.Comparison.ExcludedMiddle.IntuitionismEntailsWithholding
open TruthCore.Logic
open TruthCore.Comparison.ExcludedMiddle
/-- The intuitionist theory entails withholding excluded middle, and not
denying it: asserting `p ∨ ¬p` needs a proof of `p` or of `¬p`; an undecided
proposition's instance is therefore not asserted; and every denial of an
instance stays refuted. The withholding is derived from the theory's sourced
commitments on proof and the comparison's open premise that assertion requires
proof, not stipulated. -/
theorem intuitionismEntailsExcludedMiddleWithheld (s : Sig) (hTheory : Intuitionist s)
    (hAssertion : TruthCore.English.Iemhoff.AssertionRequiresProofReading s.Proved s.Asserts) :
    ExcludedMiddleWithheld s.Proved s.Asserts := by
  obtain ⟨hDecided, hUndecided, hIrrefutable⟩ := hTheory
  -- Asserting p ∨ ¬p requires proving it, and a proof of it is a proof of p
  -- or of ¬p.
  have hRule : ∀ st p, s.Asserts st (p ∨ ¬ p) → s.Proved st p ∨ s.Proved st (¬ p) :=
    fun st p hAsserted => hDecided st p (hAssertion st (p ∨ ¬ p) hAsserted)
  -- At a stage where p is undecided, p ∨ ¬p is not asserted.
  obtain ⟨st, p, hNotProved, hNotRefuted⟩ := hUndecided
  have hWithheld : ¬ s.Asserts st (p ∨ ¬ p) := fun hAsserted =>
    (hRule st p hAsserted).elim hNotProved hNotRefuted
  exact ⟨hRule, ⟨st, p, hWithheld⟩, hIrrefutable⟩
end TruthCore.Results.Comparison.ExcludedMiddle.IntuitionismEntailsWithholding
