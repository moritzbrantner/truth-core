import TruthCore.Space.TranslationBoundary
namespace TruthCore.Results.Space.TranslationBoundary
open TruthCore.Space.TranslationBoundary

theorem relative_shift {B : Type} (a : ℝ) (x : Configuration B) :
    relative (shift a x) = relative x := by
  funext i j
  simp [relative, shift]

theorem orbit_iff {B : Type} (b : B) (x y : Configuration B) :
    Relative x y ↔ ∃ a, y = shift a x := by
  constructor
  · intro h
    refine ⟨y b - x b, ?_⟩
    funext i
    have hi := congrFun (congrFun h i) b
    change x i - x b = y i - y b at hi
    change y i = x i + (y b - x b)
    calc
      y i = (y i - y b) + y b := (sub_add_cancel _ _).symm
      _ = (x i - x b) + y b := by rw [← hi]
      _ = x i + (y b - x b) := by abel
  · rintro ⟨a, rfl⟩
    exact (relative_shift a x).symm

theorem distances {B : Type} (a : ℝ) (x : Configuration B) (i j : B) :
    dist (shift a x i) (shift a x j) = dist (x i) (x j) := by
  simp [shift, Real.dist_eq]

theorem fixed_iff {B : Type} (b : B) (a : ℝ) (x : Configuration B) :
    shift a x = x ↔ a = 0 := by
  constructor
  · intro h
    have hi := congrFun h b
    change x b + a = x b at hi
    exact add_left_cancel (hi.trans (add_zero (x b)).symm)
  · rintro rfl
    funext i
    exact add_zero _

theorem no_covariant_selector {B : Type} (b : B) :
    ¬ ∃ select : (B → B → ℝ) → Configuration B, Covariant select := by
  rintro ⟨select, h⟩
  let x : Configuration B := fun _ => 0
  have hs := h 1 x
  rw [relative_shift] at hs
  have hz : (1 : ℝ) = 0 := (fixed_iff b 1 _).mp hs.symm
  exact one_ne_zero hz

theorem normalization {B : Type} (b : B) (a : ℝ) (x : Configuration B) :
    normal b (shift a x) = normal b x ∧ Relative x (normal b x) := by
  constructor
  · funext i
    simp [normal, shift]
  · funext i j
    change x i - x j = (x i - x b) - (x j - x b)
    abel

theorem controls : Certificate := by
  refine ⟨fun _ => orbit_iff, fun _ => distances, fun _ => fixed_iff,
    fun _ => no_covariant_selector, fun _ => normalization, ?_, ?_⟩
  · refine ⟨by norm_num [pair], by norm_num [pair], ?_, ?_, ?_⟩
    · exact (relative_shift 1 pair).symm
    · intro h
      exact one_ne_zero ((fixed_iff false 1 pair).mp h)
    · norm_num [pair, Real.dist_eq]
  · refine ⟨(fun _ e => nomatch e), ?_⟩
    intro a x
    funext e
    cases e
end TruthCore.Results.Space.TranslationBoundary
