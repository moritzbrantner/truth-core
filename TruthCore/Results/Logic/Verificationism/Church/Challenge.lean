import TruthCore.Logic.Verificationism
namespace TruthCore.Results.Logic.Verificationism.Church
open TruthCore.Logic.Verificationism
/-- Church's trivialization of Ayer's 1946 criterion: given observation statements o₁, o₂, o₃ with o₁ ⊭ o₃ and o₃ ⊭ o₂, every sentence whose negation is not directly verifiable is indirectly verifiable, through Church's sentence (¬o₁ ∧ o₂) ∨ (o₃ ∧ ¬s). -/
theorem churchTrivialization : ChurchTrivialization := by
  sorry
end TruthCore.Results.Logic.Verificationism.Church
