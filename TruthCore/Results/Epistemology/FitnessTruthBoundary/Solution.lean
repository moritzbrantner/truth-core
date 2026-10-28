import TruthCore.Epistemology.FitnessTruthBoundary
namespace TruthCore.Results.Epistemology.FitnessTruthBoundary
open TruthCore.Epistemology.FitnessTruthBoundary

private theorem compensation (b d t : Bool) : act b d = t ↔ d = Bool.xor b t := by
  cases b <;> cases d <;> cases t <;> decide

private theorem direct_iff (b d t : Bool) (h : act b d = t) : b = t ↔ d = false := by
  cases b <;> cases d <;> cases t <;> simp_all [act]

theorem certificate : Certificate := by
  refine ⟨compensation, ?_, ?_, ?_⟩
  · intro S t b
    exact ⟨fun s => Bool.xor (b s) (t s), fun s => (compensation _ _ _).mpr rfl⟩
  · intro S t b d h
    exact ⟨fun ht s => (direct_iff _ _ _ (h s)).mp (ht s),
      fun hd s => (direct_iff _ _ _ (h s)).mpr (hd s)⟩
  · refine ⟨id, (fun _ => false), Bool.not, (fun _ => true), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro s; cases s <;> rfl
    · intro s; cases s <;> rfl
    · intro s; rfl
    · intro s; cases s <;> decide
    · intro h; exact Bool.noConfusion (h false)
    · intro s; cases s <;> rfl
    · intro score
      apply congrArg score
      funext s
      cases s <;> rfl
end TruthCore.Results.Epistemology.FitnessTruthBoundary
