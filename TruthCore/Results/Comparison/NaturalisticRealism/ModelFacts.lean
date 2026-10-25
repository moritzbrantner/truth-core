import TruthCore.Results.Comparison.NaturalisticRealism.Model

namespace TruthCore.Results.Comparison.NaturalisticRealism
open TruthCore.Comparison.NaturalisticRealism

theorem modelRailton : Railton model := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x a; exact Iff.rfl
  · intro a
    cases a
    · constructor
      · intro h; exact Bool.noConfusion h
      · intro h
        have bad := h true
        exact False.elim (Nat.not_succ_le_zero 1 bad)
    · constructor
      · intro _ b; cases b <;> decide
      · intro _; rfl
  · intro φ h; trivial
  · intro φ a h
    cases φ
    · cases a
      · exact Bool.noConfusion h
      · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · cases a
      · exact ⟨Bool.noConfusion, Bool.noConfusion⟩
      · exact Bool.noConfusion h

theorem modelBoyd : Boyd model := by
  refine ⟨?_, ?_, ?_⟩
  · intro a h
    cases h with
    | inl h => exact h
    | inr h => exact h
  · intro φ h; trivial
  · intro φ a h
    cases φ
    · cases a
      · exact Bool.noConfusion h
      · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · cases a
      · exact ⟨Bool.noConfusion, Bool.noConfusion⟩
      · exact Bool.noConfusion h

end TruthCore.Results.Comparison.NaturalisticRealism
