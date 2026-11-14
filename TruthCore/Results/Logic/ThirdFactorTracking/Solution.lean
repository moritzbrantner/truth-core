module

public import TruthCore.Logic.ThirdFactorTracking

/-! The third-factor union bound, exact binary error accounting, the subclass
gap bound and the finite sharpness, cancellation and hard-case models for
#1586. No independence between the error events is assumed. -/

@[expose] public section
namespace TruthCore.Results.Logic.ThirdFactorTracking
open TruthCore.Logic.ThirdFactorTracking
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

private theorem disagree_subset {Ω V : Type} (B F M : Ω → V) :
    disagree B M ⊆ disagree B F ∪ disagree F M := by
  intro ω h
  by_contra hc
  simp only [disagree, mem_union, mem_ofPred_eq, not_or, not_not] at h hc
  exact h (hc.1.trans hc.2)

private theorem agree_compl {Ω V : Type} (B M : Ω → V) : agree B M = (disagree B M)ᶜ := by
  ext ω; simp [agree, disagree]

/-- Third-factor union bound on one common distribution, without independence:
`{B ≠ M} ⊆ {B ≠ F} ∪ {F ≠ M}` and subadditivity. Values may be of any type. -/
theorem thirdFactorUnionBound {Ω V : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (B F M : Ω → V) (e₁ e₂ : ℝ≥0∞) :
    SelectionErrorAtMost μ B F e₁ →
    FactorTruthGapAtMost μ F M e₂ →
    JudgmentTruthAgreementAtLeast μ B M (e₁ + e₂) := by
  intro h₁ h₂
  have hle : μ (disagree B M) ≤ e₁ + e₂ :=
    (measure_mono (disagree_subset B F M)).trans
      ((measure_union_le _ _).trans (add_le_add h₁ h₂))
  refine ⟨hle, fun hP hm => ?_⟩
  have hd : MeasurableSet (disagree B M) := by
    rw [agree_compl] at hm; simpa using hm.compl
  rw [agree_compl, prob_compl_eq_one_sub hd]
  exact tsub_le_tsub_left hle 1

private theorem disagree_bool {Ω : Type} (B F M : Ω → Bool) :
    disagree B M = symmDiff (disagree B F) (disagree F M) := by
  ext ω
  simp only [disagree, mem_ofPred_eq, Set.mem_symmDiff]
  cases B ω <;> cases F ω <;> cases M ω <;> simp

/-- Exact binary error accounting: two errors cancel. -/
theorem binaryErrorAccounting : BinaryErrorAccounting := by
  intro Ω _ μ B F M hX hY
  set X := disagree B F
  set Y := disagree F M
  have hsym := disagree_bool B F M
  have hid : μ (disagree B M) + 2 * μ (X ∩ Y) = μ X + μ Y := by
    rw [hsym, measure_symmDiff_eq hX.nullMeasurableSet hY.nullMeasurableSet, two_mul]
    rw [← measure_sdiff_add_inter X hY, ← measure_sdiff_add_inter Y hX, inter_comm Y X]
    ring
  refine ⟨hsym, hid, fun hfin => ?_⟩
  have hfinite : μ X + μ Y ≠ ∞ := by finiteness
  constructor
  · intro h
    rw [h] at hid
    have h2 : 2 * μ (X ∩ Y) = 0 := by
      have := (ENNReal.add_right_inj hfinite).mp (hid.trans (add_zero _).symm)
      exact this
    simpa using h2
  · intro h
    rw [h, mul_zero, add_zero] at hid
    exact hid

/-- The gap on a measurable class is at most the aggregate gap divided by the
class weight. -/
theorem subclassGapBound : SubclassGapBound := by
  intro Ω V _ μ F M S hS
  rw [cond_apply hS, ENNReal.div_eq_inv_mul]
  gcongr
  exact inter_subset_right

private theorem cases4_apply (s : Finset (Fin 4)) :
    cases4 (s : Set (Fin 4)) = s.card / 4 := by
  rw [cases4, ← Finset.coe_univ, uniformOn_apply_finset]
  simp

private theorem cases4_prob : IsProbabilityMeasure cases4 := by
  unfold cases4; infer_instance

private theorem set_eq (P : Fin 4 → Prop) [DecidablePred P] :
    {ω | P ω} = ((Finset.univ.filter P : Finset (Fin 4)) : Set (Fin 4)) := by
  ext ω; simp

private theorem cond_cases4 (S t : Finset (Fin 4)) :
    cases4[(t : Set (Fin 4)) | (S : Set (Fin 4))] = (S ∩ t).card / S.card := by
  rw [cond_apply (Finset.measurableSet _), ← Finset.coe_inter, cases4_apply, cases4_apply]
  rcases Nat.eq_zero_or_pos S.card with h | h
  · simp [Finset.card_eq_zero.mp h]
  · have h4 : (4 : ℝ≥0∞) ≠ 0 := by norm_num
    have hS : (S.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast h.ne'
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
      ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 (by norm_num)))
        (Or.inl (ENNReal.inv_ne_top.2 h4)), inv_inv]
    rw [show (4 : ℝ≥0∞) * (S.card : ℝ≥0∞)⁻¹ * ((4 : ℝ≥0∞)⁻¹ * ((S ∩ t).card : ℝ≥0∞))
        = ((4 : ℝ≥0∞) * (4 : ℝ≥0∞)⁻¹) * ((S.card : ℝ≥0∞)⁻¹ * ((S ∩ t).card)) by ring,
      ENNReal.mul_inv_cancel h4 (by norm_num), one_mul]

private theorem cases4_finset (A : Set (Fin 4)) (s : Finset (Fin 4)) (h : A = s) :
    cases4 A = s.card / 4 := by
  rw [h, cases4_apply]

/-- Sharpness, cancellation and hard-case concentration in four stipulated cases. -/
theorem thirdFactorModels : ThirdFactorModels := by
  have hP := cases4_prob
  have e0 : disagree judgmentOff0 factorAll = (({0} : Finset (Fin 4)) : Set (Fin 4)) := by
    ext ω; fin_cases ω <;> simp [disagree, judgmentOff0, factorAll]
  have e0' : disagree factorAll judgmentOff0 = (({0} : Finset (Fin 4)) : Set (Fin 4)) := by
    ext ω; fin_cases ω <;> simp [disagree, judgmentOff0, factorAll]
  have e1 : disagree factorAll truthOff1 = (({1} : Finset (Fin 4)) : Set (Fin 4)) := by
    ext ω; fin_cases ω <;> simp [disagree, truthOff1, factorAll]
  have a23 : agree judgmentOff0 truthOff1 = (({2, 3} : Finset (Fin 4)) : Set (Fin 4)) := by
    ext ω; fin_cases ω <;> simp [agree, judgmentOff0, truthOff1]
  have aself : agree judgmentOff0 judgmentOff0 = univ := by ext ω; simp [agree]
  have dself : disagree factorAll factorAll = ∅ := by ext ω; simp [disagree]
  have e3 : disagree factorAll truthHard = (({3} : Finset (Fin 4)) : Set (Fin 4)) := by
    ext ω; fin_cases ω <;> simp [disagree, truthHard, factorAll]
  have a012 : agree factorAll truthHard = (({0, 1, 2} : Finset (Fin 4)) : Set (Fin 4)) := by
    ext ω; fin_cases ω <;> simp [agree, truthHard, factorAll]
  have hh : hardCase = (({3} : Finset (Fin 4)) : Set (Fin 4)) := by simp [hardCase]
  have hc : hardCaseᶜ = (({0, 1, 2} : Finset (Fin 4)) : Set (Fin 4)) := by
    ext ω; fin_cases ω <;> simp [hardCase]
  have q : cases4 (disagree factorAll truthHard) = 1/4 := by
    rw [cases4_finset _ _ e3]; simp
  have qh : cases4 hardCase = 1/4 := by rw [cases4_finset _ _ hh]; simp
  refine ⟨hP, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, q, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [cases4_finset _ _ e0]; simp
  · rw [cases4_finset _ _ e1]; simp
  · rw [cases4_finset _ _ a23, show ({2, 3} : Finset (Fin 4)).card = 2 by decide,
      ENNReal.div_eq_div_iff] <;> norm_num
  · rw [cases4_finset _ _ e0]; simp
  · rw [cases4_finset _ _ e0']; simp
  · rw [aself, measure_univ]
  · rw [dself, measure_empty]
  · rw [cases4_finset _ _ a012, show ({0, 1, 2} : Finset (Fin 4)).card = 3 by decide]; norm_num
  · rw [a012, hh, cond_cases4, show ({3} ∩ {0, 1, 2} : Finset (Fin 4)).card = 0 by decide]
    simp
  · rw [a012, hc, cond_cases4, Finset.inter_self,
      show ({0, 1, 2} : Finset (Fin 4)).card = 3 by decide]
    exact ENNReal.div_self (by norm_num) (by norm_num)
  · rw [e3, hh, cond_cases4, Finset.inter_self]; simp
  · rw [q, qh]; exact ENNReal.div_self (by norm_num) (by norm_num)

end TruthCore.Results.Logic.ThirdFactorTracking
