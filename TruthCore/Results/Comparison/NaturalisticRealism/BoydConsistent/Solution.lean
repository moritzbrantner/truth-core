import TruthCore.Results.Comparison.NaturalisticRealism.Model
namespace TruthCore.Results.Comparison.NaturalisticRealism.BoydConsistent
open TruthCore.Metaethics.NaturalisticRealism
open TruthCore.Comparison.NaturalisticRealism

theorem boydConsistent : BoydConsistent := by
  refine ⟨model, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
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
  · exact ⟨false, true, trivial, trivial, trivial, Bool.noConfusion⟩
  · exact ⟨false, true, rfl, id⟩
  · exact ⟨false, trivial, rfl⟩

end TruthCore.Results.Comparison.NaturalisticRealism.BoydConsistent
