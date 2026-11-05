module
public import TruthCore.Explanation.ActualExistenceAdequacy
public import TruthCore.Results.Modern.Hume.Regularity.Solution
@[expose] public section
namespace TruthCore.Results.Explanation.ActualExistenceAdequacy
open TruthCore.Explanation.ActualExistenceAdequacy
open TruthCore.Explanation.PSRStrength
open TruthCore.Modern.Hume.Regularity

private theorem target (m : Experiment) (hy : m.y = id) : Target m := by
  refine ⟨fun _ _ => Iff.rfl, trivial, ?_, ?_, ?_⟩
  · change m.y true = true
    rw [hy]
    rfl
  · refine ⟨?_, false, trivial, ?_⟩
    · change m.y true = true
      rw [hy]
      rfl
    · change ¬ m.y false = true
      rw [hy]
      decide
  · refine ⟨?_, false, trivial, ?_⟩
    · change m.y true = true
      rw [hy]
      rfl
    · change ¬ m.y false = true
      rw [hy]
      decide

private theorem independent : VerificationIndependent (fun v => eval v .reason) := by
  refine ⟨[(.reason, true)], ?_, ?_, ?_, (true, true), ?_, Iff.rfl⟩
  · intro l hl
    simp only [List.mem_singleton] at hl
    subst l
    rfl
  · intro v hv
    exact hv (.reason, true) (by simp)
  · intro h
    have bad := h (true, false) ?_
    · exact Bool.noConfusion bad
    · intro l hl
      simp only [List.mem_singleton] at hl
      subst l
      rfl
  · intro l hl
    simp only [List.mem_singleton] at hl
    subst l
    rfl

private theorem copied : ¬ VerificationIndependent (fun v => eval v .target) := by
  rintro ⟨_, _, entails, notEntails, _⟩
  exact notEntails entails

 theorem comparison : Comparison := by
  refine ⟨target chain rfl, target fork rfl, fun _ _ => Iff.rfl,
    fun w f => ?_, independent, copied, fun _ => Iff.rfl, ?_, ?_⟩
  · cases f <;> exact Iff.rfl
  · exact TruthCore.Results.Modern.Hume.Regularity.checks.2.2.2.2.1.2.1
  · exact TruthCore.Results.Modern.Hume.Regularity.checks.2.2.2.2.1.2.2.1
end TruthCore.Results.Explanation.ActualExistenceAdequacy
