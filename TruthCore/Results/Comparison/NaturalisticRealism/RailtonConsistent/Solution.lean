import TruthCore.Results.Comparison.NaturalisticRealism.Model
namespace TruthCore.Results.Comparison.NaturalisticRealism.RailtonConsistent
open TruthCore.Metaethics.NaturalisticRealism
open TruthCore.Comparison.NaturalisticRealism

theorem railtonConsistent : RailtonConsistent := by
  refine ⟨model, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
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
  · exact ⟨false, true, trivial, trivial, trivial, Bool.noConfusion⟩
  · exact ⟨false, true, rfl, id⟩
  · exact ⟨false, trivial, rfl⟩

end TruthCore.Results.Comparison.NaturalisticRealism.RailtonConsistent
