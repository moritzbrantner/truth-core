import TruthCore.Comparison.ExcludedMiddle
import TruthCore.Results.Logic.ExcludedMiddleIrrefutable.Solution
namespace TruthCore.Results.Comparison.ExcludedMiddle.IntuitionistTheoryConsistent
open TruthCore.Logic
open TruthCore.English.Iemhoff
open TruthCore.Comparison.ExcludedMiddle
/-- The intuitionist theory is consistent. Model: two stages, `false` (now)
and `true` (an idealized later stage); at `true` exactly the true propositions
are proved, at `false` none is; what is asserted is what is proved. Every
commitment holds constructively, so the rival does not lose on consistency; the
comparison turns on what it leaves unexplained. -/
theorem intuitionistTheoryConsistent : IntuitionistTheoryConsistent := by
  unfold IntuitionistTheoryConsistent Intuitionist
  refine ⟨⟨Bool, fun st p => st = true ∧ p, fun st p => st = true ∧ p⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- A proof of p ∨ ¬p at the later stage is a proof of p or of ¬p there.
    intro st p hProved
    cases hProved.2 with
    | inl hp => exact Or.inl ⟨hProved.1, hp⟩
    | inr hnp => exact Or.inr ⟨hProved.1, hnp⟩
  · -- Now, nothing is proved: `True` is undecided at stage `false`.
    unfold SomePropositionUndecidedReading
    refine ⟨false, True, ?_, ?_⟩
    · intro hProved
      exact Bool.noConfusion hProved.1
    · intro hRefuted
      exact Bool.noConfusion hRefuted.1
  · -- What is asserted is what is proved.
    intro st p hAsserted
    exact hAsserted
  · -- No instance of excluded middle is refutable (LOGIC-EXCLUDED-MIDDLE-IRREFUTABLE).
    exact TruthCore.Results.Logic.ExcludedMiddleIrrefutable.excludedMiddleIrrefutable
  · -- A proposition holds exactly when it is proved at some stage: at `true`.
    intro p
    constructor
    · intro hp
      exact ⟨true, rfl, hp⟩
    · intro ⟨_, _, hp⟩
      exact hp
end TruthCore.Results.Comparison.ExcludedMiddle.IntuitionistTheoryConsistent
