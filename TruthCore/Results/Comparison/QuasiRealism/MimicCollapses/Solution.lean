import TruthCore.Metaethics.AnswerMap
namespace TruthCore.Results.Comparison.QuasiRealism.MimicCollapses
open TruthCore.Metaethics

/-- The collapse lemma. If `T` matches `R` on every question, then at each
question where `R` answers and its answer holds, `T` answers (the answers
agree on whether there is one) and its equivalent answer holds too. And no
question is one where `T` deviates, so `T` is not a distinct rival. -/
theorem mimicCollapses : MimicCollapses := by
  intro Q T R hMimics
  refine ⟨?_, ?_⟩
  · -- INF-MIMIC-INHERITS-COMMITMENTS
    intro q hCommitted
    have hAnswered : T.answers q := (hMimics q).1.mpr hCommitted.1
    exact ⟨hAnswered, ((hMimics q).2 hAnswered).mpr hCommitted.2⟩
  · -- INF-MIMIC-IS-NO-DISTINCT-RIVAL
    intro ⟨q, hDeviates⟩
    exact hDeviates (hMimics q)

end TruthCore.Results.Comparison.QuasiRealism.MimicCollapses
