module
public import TruthCore.Results.Explanation.ActualExistenceAdequacy.Solution
@[expose] public section
namespace TruthCore.Results.Explanation.ActualExistenceAdequacy
open TruthCore.Explanation.ActualExistenceAdequacy
open TruthCore.Modern.Hume.Regularity

private theorem richTarget (m : Experiment) (hy : m.y = id) : RealizedTarget m := by
  refine ⟨fun _ _ => Iff.rfl, trivial, ?_, ?_, ?_⟩
  · change m.y true = true
    rw [hy]
    rfl
  · refine ⟨?_, .inl false, trivial, ?_⟩
    · change m.y true = true
      rw [hy]
      rfl
    · change ¬ m.y false = true
      rw [hy]
      decide
  · refine ⟨?_, .inl false, trivial, ?_⟩
    · change m.y true = true
      rw [hy]
      rfl
    · change ¬ m.y false = true
      rw [hy]
      decide

theorem realization : RealizationComparison := by
  refine ⟨richTarget chain rfl, richTarget fork rfl, fun _ _ _ => Iff.rfl,
    ?_, fun _ _ _ => Iff.rfl, ?_, ?_, ?_, comparison.2.2.2.2.1⟩
  · intro w f
    cases f <;> exact Iff.rfl
  · refine ⟨false, ?_⟩
    intro h
    exact Bool.noConfusion (h.mpr rfl)
  · rintro ⟨u, h⟩
    exact h Iff.rfl
  · intro h
    exact Bool.noConfusion (h.mpr rfl)
end TruthCore.Results.Explanation.ActualExistenceAdequacy
