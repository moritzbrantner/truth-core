module

public import TruthCore.Logic.FiniteValidationLogic
public import Mathlib.Tactic.GCongr

/-! Product-measure validation and explicit selection boundaries for #1066.
No expert budget or realizability premise is imported or assumed. -/

@[expose] public section
namespace TruthCore.Results.Logic.FiniteValidationLogic
open TruthCore.Logic.FiniteValidationLogic
open MeasureTheory
open scoped ENNReal NNReal

private theorem passProbability {Ω : Type} [Fintype Ω] [MeasurableSpace Ω]
    [DiscreteMeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (truth h : Ω → Bool) (n : ℕ) :
    sampling μ n (passes truth h n) = (1-error μ truth h)^n := by
  have he : {x | h x = truth x} = {x | h x ≠ truth x}ᶜ := by ext; simp
  have hp : passes truth h n = Set.pi Set.univ (fun _ : Fin n => {x | h x = truth x}) := by
    ext s; simp [passes]
  rw [hp, sampling, Measure.pi_pi]
  simp only [he, measure_compl MeasurableSet.of_discrete (measure_ne_top _ _), measure_univ]
  simp [error]

/-- Exact validation probabilities and predeclared finite-pool false-acceptance
control under the explicit independent sampling profile; no realizability. -/
theorem samplingCertificate : SamplingCertificate := by
  intro Ω _ _ _ μ _ truth h n
  refine ⟨passProbability μ truth h n, ?_⟩
  intro pool ε _
  classical
  let events : (Ω → Bool) → Set (Fin n → Ω) := fun h =>
    if ε < error μ truth h then passes truth h n else ∅
  have he : falseAcceptance μ truth pool ε n = ⋃ h ∈ pool, events h := by
    ext s; simp [falseAcceptance, events]; aesop
  rw [he]
  calc
    sampling μ n (⋃ h ∈ pool, events h) ≤ ∑ h ∈ pool, sampling μ n (events h) :=
      measure_biUnion_finset_le pool events
    _ ≤ ∑ _h ∈ pool, (1-ε)^n := by
      apply Finset.sum_le_sum
      intro h hh
      dsimp [events]
      split_ifs with hb
      · rw [passProbability]
        exact pow_le_pow_left' (tsub_le_tsub_left (le_of_lt hb) 1) n
      · simp
    _ = (pool.card : ℝ≥0∞) * (1-ε)^n := by simp [nsmul_eq_mul]

private theorem quarterComplement : (1:ℝ≥0∞) - 4⁻¹ = 3/4 := by
  rw [show (4:ℝ≥0∞) = ((4:ℝ≥0):ℝ≥0∞) from rfl, ← ENNReal.coe_inv (by norm_num)]
  change ((1:ℝ≥0):ℝ≥0∞) - _ = ((3:ℝ≥0):ℝ≥0∞)/_
  rw [← ENNReal.coe_div (by norm_num), ← ENNReal.coe_sub]
  norm_cast
  apply NNReal.eq
  norm_num [NNReal.coe_sub_def]

private theorem threeQuarterComplement : (1:ℝ≥0∞) - 3/4 = 1/4 := by
  change ((1:ℝ≥0):ℝ≥0∞) - ((3:ℝ≥0):ℝ≥0∞)/((4:ℝ≥0):ℝ≥0∞) =
    ((1:ℝ≥0):ℝ≥0∞)/((4:ℝ≥0):ℝ≥0∞)
  rw [← ENNReal.coe_div (by norm_num), ← ENNReal.coe_div (by norm_num), ← ENNReal.coe_sub]
  norm_cast
  apply NNReal.eq
  norm_num [NNReal.coe_sub_def]

private theorem halfLtThreeQuarter : (1/2:ℝ≥0∞) < 3/4 := by
  change ((1:ℝ≥0):ℝ≥0∞)/((2:ℝ≥0):ℝ≥0∞) < ((3:ℝ≥0):ℝ≥0∞)/((4:ℝ≥0):ℝ≥0∞)
  rw [← ENNReal.coe_div (by norm_num), ← ENNReal.coe_div (by norm_num), ENNReal.coe_lt_coe]
  norm_num

private theorem uniformProbability : IsProbabilityMeasure uniformFour := by
  constructor
  norm_num [uniformFour, Measure.uniformOfFinset_apply, ENNReal.div_self]

private theorem memorizerError (seen : Fin 4) :
    error uniformFour (fun _ => false) (memorizer seen) = 3/4 := by
  have := uniformProbability
  have he : {x | memorizer seen x ≠ false} = ({seen} : Set (Fin 4))ᶜ := by
    ext x; simp [memorizer]
  rw [error, he, measure_compl MeasurableSet.of_discrete (measure_ne_top _ _), measure_univ]
  simpa [uniformFour] using quarterComplement

/-- Explicit posthoc-selection and frequentist/posterior boundary controls. -/
theorem selectionControls : SelectionControls := by
  have := uniformProbability
  have hp : ∀ s : Fin 1 → Fin 4,
      s ∈ passes (fun _ => false) (memorizer (s 0)) 1 := by
    intro s i
    have hi : i = 0 := Subsingleton.elim _ _
    simp [hi, memorizer]
  refine ⟨uniformProbability, memorizerError, hp, ?_, ?_, ?_⟩
  · have he : {s : Fin 1 → Fin 4 | (1/2 : ℝ≥0∞) <
        error uniformFour (fun _ => false) (memorizer (s 0)) ∧
        s ∈ passes (fun _ => false) (memorizer (s 0)) 1} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro s
      exact ⟨by rw [memorizerError]; exact halfLtThreeQuarter, hp s⟩
    rw [he]
    exact @measure_univ _ _ (Measure.pi (fun _ : Fin 1 => uniformFour)) inferInstance
  · norm_num
  · intro n
    have hprob : sampling uniformFour n (passes (fun _ => false) (memorizer 0) n) =
        (1/4 : ℝ≥0∞)^n := by
      rw [passProbability, memorizerError]
      rw [threeQuarterComplement]
    refine ⟨hprob, ?_, ?_⟩
    · rw [hprob]
      exact ENNReal.pow_pos (ENNReal.div_pos (by norm_num) (by norm_num)) n
    · ext s
      change (_ ∧ _) ↔ _
      rw [memorizerError]
      exact and_iff_right halfLtThreeQuarter

end TruthCore.Results.Logic.FiniteValidationLogic
