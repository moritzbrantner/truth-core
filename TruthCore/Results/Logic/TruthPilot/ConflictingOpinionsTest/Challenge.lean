import TruthCore.Logic.TruthPilot
namespace TruthCore.Results.Logic.TruthPilot.ConflictingOpinionsTest
open TruthCore.Logic.TruthPilot
/-- Test Aristotle’s reported all-opinions-true target only under an explicit interpretation of expressed negation. No refutes relation against every relativism or against withholding. -/
theorem conflictingOpinionsTest {Person Content : Type} (Opines : Person → Content → Prop)
    (TrueAtIssue : Content → Prop) (neg : Content → Content)
    (hConflict : ConflictingOpinions Opines neg)
    (hNegation : NegationRespected TrueAtIssue neg) : NotAllOpinionsTrue Opines TrueAtIssue := by
  sorry
end TruthCore.Results.Logic.TruthPilot.ConflictingOpinionsTest
