import TruthCore.Logic.TruthPilot
namespace TruthCore.Results.Logic.TruthPilot.ConflictingOpinionsTest
open TruthCore.Logic.TruthPilot
/-- Test Aristotle’s reported all-opinions-true target only under an explicit interpretation of expressed negation. No refutes relation against every relativism or against withholding. -/
theorem conflictingOpinionsTest {Person Content : Type} (Opines : Person → Content → Prop)
    (TrueAtIssue : Content → Prop) (neg : Content → Content)
    (hConflict : ConflictingOpinions Opines neg)
    (hNegation : NegationRespected TrueAtIssue neg) : NotAllOpinionsTrue Opines TrueAtIssue := by
  intro hAll
  obtain ⟨a, b, p, hOpinion, hOpposite⟩ := hConflict
  have hTrue := hAll a p hOpinion
  have hNegated := hAll b (neg p) hOpposite
  exact hNegation p hNegated hTrue
/-- Without the negation bridge, opposed expressed contents and universally true
opinions coexist in a model. This is not a source attribution or a defense of
a complete worldview. -/
theorem conflictWithoutLogicalNegation :
    ∃ (Opines : Unit → Bool → Prop) (TrueAtIssue : Bool → Prop) (neg : Bool → Bool),
      AllOpinionsTrue Opines TrueAtIssue ∧ ConflictingOpinions Opines neg ∧
        ¬ NegationRespected TrueAtIssue neg := by
  refine ⟨(fun _ _ => True), (fun _ => True), Bool.not, ?_, ?_, ?_⟩
  · intro a p hOpinion
    trivial
  · exact ⟨(), (), true, trivial, trivial⟩
  · intro hNegation
    exact hNegation true trivial trivial

/-- Without conflicting opinions, truth respecting ordinary Boolean negation is
compatible with the all-opinions-true schema (vacuously, when no one opines). -/
theorem noConflictWithLogicalNegation :
    ∃ (Opines : Unit → Bool → Prop) (TrueAtIssue : Bool → Prop) (neg : Bool → Bool),
      AllOpinionsTrue Opines TrueAtIssue ∧ NegationRespected TrueAtIssue neg ∧
        ¬ ConflictingOpinions Opines neg := by
  refine ⟨(fun _ _ => False), (fun p => p = true), Bool.not, ?_, ?_, ?_⟩
  · intro a p hOpinion
    exact hOpinion.elim
  · intro p hNegated hTrue
    cases p with
    | false => cases hTrue
    | true => cases hNegated
  · intro hConflict
    obtain ⟨a, b, p, hOpinion, hOpposite⟩ := hConflict
    exact hOpinion

end TruthCore.Results.Logic.TruthPilot.ConflictingOpinionsTest
