module

public import TruthCore.Logic.PrefaceConnectivity
public import Mathlib.Tactic.Linarith

/-! Exact profile probabilities, the marginals/joint separation, the Makinson
boundary, local cross-check posteriors and coverage-explicit elimination for
#1584. Every probability is computed in the stipulated product profile. -/

@[expose] public section
namespace TruthCore.Results.Logic.PrefaceConnectivity
open TruthCore.Logic.PrefaceConnectivity
open TruthCore.Logic.ThresholdBelief (Accepted)
open TruthCore.Logic.ReflectiveCoherence
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

private theorem allTrue_eq {Γ Λ : Type} (G : Set Γ) (C : Set Λ) {n : ℕ} (hn : 0 < n) :
    allTrue G C n = G ×ˢ Set.pi univ (fun _ => C) := by
  ext ⟨g, ω⟩
  simp only [allTrue, assertion, mem_iInter, mem_ofPred_eq, mem_prod, mem_pi, mem_univ,
    true_implies]
  exact ⟨fun h => ⟨(h ⟨0, hn⟩).1, fun i => (h i).2⟩, fun h i => ⟨h.1, h.2 i⟩⟩

private theorem someFalse_eq {Γ Λ : Type} (G : Set Γ) (C : Set Λ) (n : ℕ) :
    someFalse G C n = (allTrue G C n)ᶜ := by
  simp [someFalse, allTrue, compl_iInter]

private theorem noFlag_eq {Γ Λ : Type} (F : Set Λ) (n : ℕ) :
    (noFlag F n : Set (Γ × (Fin n → Λ))) = univ ×ˢ Set.pi univ (fun _ => Fᶜ) := by
  ext ⟨g, ω⟩; simp [noFlag]

private theorem allTrue_noFlag_eq {Γ Λ : Type} (G : Set Γ) (C F : Set Λ) {n : ℕ}
    (hn : 0 < n) :
    allTrue G C n ∩ noFlag F n = G ×ˢ Set.pi univ (fun _ => C ∩ Fᶜ) := by
  rw [allTrue_eq G C hn, noFlag_eq]
  ext ⟨g, ω⟩
  simp only [mem_inter_iff, mem_prod, mem_pi, mem_univ, true_implies, true_and,
    mem_compl_iff]
  exact ⟨fun h => ⟨h.1.1, fun i => ⟨h.1.2 i, h.2 i⟩⟩,
    fun h => ⟨⟨h.1, fun i => (h.2 i).1⟩, fun i => (h.2 i).2⟩⟩

private theorem profileBox {Γ Λ : Type} [MeasurableSpace Γ] [MeasurableSpace Λ]
    (κ : Measure Γ) (ν : Measure Λ) [IsProbabilityMeasure ν]
    (A : Set Γ) (S : Set Λ) (n : ℕ) :
    profile κ ν n (A ×ˢ Set.pi univ (fun _ => S)) = κ A * ν S ^ n := by
  rw [profile, Measure.prod_prod, Measure.pi_pi]
  simp

private instance profileProb {Γ Λ : Type} [MeasurableSpace Γ] [MeasurableSpace Λ]
    (κ : Measure Γ) [IsProbabilityMeasure κ] (ν : Measure Λ) [IsProbabilityMeasure ν]
    (n : ℕ) : IsProbabilityMeasure (profile κ ν n) := by
  rw [profile]; infer_instance

private theorem assertion_prob {Γ Λ : Type} [MeasurableSpace Γ] [MeasurableSpace Λ]
    [DiscreteMeasurableSpace Λ] (κ : Measure Γ) (ν : Measure Λ) [IsProbabilityMeasure ν]
    (G : Set Γ) (C : Set Λ) {n : ℕ} (i : Fin n) :
    profile κ ν n (assertion G C i) = κ G * ν C := by
  have h : assertion G C i = G ×ˢ ((fun ω : Fin n → Λ => ω i) ⁻¹' C) := by
    ext ⟨g, ω⟩; simp [assertion]
  rw [h, profile, Measure.prod_prod,
    (measurePreserving_eval (fun _ : Fin n => ν) i).measure_preimage
      MeasurableSet.of_discrete.nullMeasurableSet]

private theorem allTrue_prob {Γ Λ : Type} [MeasurableSpace Γ] [MeasurableSpace Λ]
    (κ : Measure Γ) (ν : Measure Λ) [IsProbabilityMeasure ν]
    (G : Set Γ) (C : Set Λ) {n : ℕ} (hn : 0 < n) :
    profile κ ν n (allTrue G C n) = κ G * ν C ^ n := by
  rw [allTrue_eq G C hn, profileBox]

private theorem someFalse_prob {Γ Λ : Type} [Fintype Γ] [MeasurableSpace Γ]
    [DiscreteMeasurableSpace Γ] [Fintype Λ] [MeasurableSpace Λ] [DiscreteMeasurableSpace Λ]
    (κ : Measure Γ) [IsProbabilityMeasure κ] (ν : Measure Λ) [IsProbabilityMeasure ν]
    (G : Set Γ) (C : Set Λ) {n : ℕ} (hn : 0 < n) :
    profile κ ν n (someFalse G C n) = 1 - κ G * ν C ^ n := by
  rw [someFalse_eq, measure_compl MeasurableSet.of_discrete (measure_ne_top _ _),
    measure_univ, allTrue_prob κ ν G C hn]

private theorem noFlag_prob {Γ Λ : Type} [MeasurableSpace Γ] [MeasurableSpace Λ]
    (κ : Measure Γ) [IsProbabilityMeasure κ] (ν : Measure Λ) [IsProbabilityMeasure ν]
    (F : Set Λ) (n : ℕ) :
    profile κ ν n (noFlag F n) = ν Fᶜ ^ n := by
  rw [noFlag_eq, profileBox, measure_univ, one_mul]

private theorem allTrue_noFlag_prob {Γ Λ : Type} [MeasurableSpace Γ] [MeasurableSpace Λ]
    (κ : Measure Γ) (ν : Measure Λ) [IsProbabilityMeasure ν]
    (G : Set Γ) (C F : Set Λ) {n : ℕ} (hn : 0 < n) :
    profile κ ν n (allTrue G C n ∩ noFlag F n) = κ G * ν (C ∩ Fᶜ) ^ n := by
  rw [allTrue_noFlag_eq G C F hn, profileBox]

private theorem noFlag_assertion_prob {Γ Λ : Type} [MeasurableSpace Γ]
    [MeasurableSpace Λ] (κ : Measure Γ) (ν : Measure Λ) [IsProbabilityMeasure ν]
    (G : Set Γ) (C F : Set Λ) {m : ℕ} (i : Fin (m + 1)) :
    profile κ ν (m + 1) (noFlag F (m + 1) ∩ assertion G C i) =
      κ G * ν (C ∩ Fᶜ) * ν Fᶜ ^ m := by
  classical
  have h : (noFlag F (m + 1) ∩ assertion G C i : Set (Γ × (Fin (m + 1) → Λ))) =
      G ×ˢ Set.pi univ (Function.update (fun _ => Fᶜ) i (C ∩ Fᶜ)) := by
    ext ⟨g, ω⟩
    simp only [noFlag, assertion, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_pi,
      mem_univ, true_implies]
    constructor
    · rintro ⟨hnf, hg, hc⟩
      refine ⟨hg, fun j => ?_⟩
      by_cases hj : j = i
      · subst hj; simpa using ⟨hc, hnf j⟩
      · simpa [Function.update_of_ne hj] using hnf j
    · rintro ⟨hg, hω⟩
      refine ⟨fun j => ?_, hg, ?_⟩
      · by_cases hj : j = i
        · subst hj
          have hj := hω j
          rw [Function.update_self] at hj
          exact hj.2
        · simpa [Function.update_of_ne hj] using hω j
      · have hi := hω i
        rw [Function.update_self] at hi
        exact hi.1
  have hfun : (fun j => ν (Function.update (fun _ => Fᶜ) i (C ∩ Fᶜ) j)) =
      Function.update (fun _ => ν Fᶜ) i (ν (C ∩ Fᶜ)) := by
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [h, profile, Measure.prod_prod, Measure.pi_pi, hfun,
    Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp [Finset.prod_const, Finset.card_sdiff, mul_assoc]

/-- Exact probabilities in the stipulated shared-plus-local product profile. -/
theorem profileProbabilities : ProfileProbabilities := by
  intro Γ Λ _ _ _ _ _ _ κ _ ν _ G C F n hn
  exact ⟨fun i => assertion_prob κ ν G C i, allTrue_prob κ ν G C hn,
    someFalse_prob κ ν G C hn, noFlag_prob κ ν F n, allTrue_noFlag_prob κ ν G C F hn⟩

/-- Same per-assertion probability, different joint probability; repetition of
one evidence event adds nothing to conditioning. -/
theorem marginalsUnderdetermineJoint : MarginalsUnderdetermineJoint := by
  refine ⟨?_, ?_⟩
  · intro Γ Λ _ _ _ _ _ _ κ _ ν _ G C q n hq0 hq1 hn
    have hn0 : 0 < n := by omega
    refine ⟨fun hG (hC : ν C = 1) => ⟨fun i => ?_, ?_, ?_⟩,
      fun (hG : κ G = 1) hC => ⟨fun i => ?_, ?_, ?_⟩⟩
    · rw [assertion_prob, hG, hC, mul_one]
    · rw [allTrue_prob κ ν G C hn0, hG, hC, one_pow, mul_one]
    · rw [someFalse_prob κ ν G C hn0, hG, hC, one_pow, mul_one]
    · rw [assertion_prob, hG, hC, one_mul]
    · rw [allTrue_prob κ ν G C hn0, hG, hC, one_mul]
    · have hq0' : q ≠ 0 := ne_of_gt hq0
      have hqt : q ≠ ⊤ := ne_top_of_lt hq1
      calc q ^ n ≤ q ^ 2 := pow_le_pow_right_of_le_one' hq1.le hn
        _ = q * q := sq q
        _ < 1 * q := ENNReal.mul_lt_mul_left hq0' hqt hq1
        _ = q := one_mul q
  · intro Ω ι _ _ μ E
    simp [iInter_const]

/-- Makinson boundary: pure shared dependence blocks joint acceptance above one
half; any local error restores acceptance of some failure for large `n`. -/
theorem hierarchicalPrefaceBoundary : HierarchicalPrefaceBoundary := by
  intro Γ Λ _ _ _ _ _ _ κ _ ν _ G C
  have hG1 : κ G ≤ 1 := prob_le_one
  refine ⟨fun (hC : ν C = 1) t ht n i ⟨ha, hs⟩ => ?_, fun hC t ht => ?_⟩
  · have hn : 0 < n := Fin.pos i
    simp only [Accepted, measureReal_def] at ha hs
    rw [assertion_prob, hC, mul_one] at ha
    rw [someFalse_prob κ ν G C hn, hC, one_pow, mul_one,
      ENNReal.toReal_sub_of_le hG1 ENNReal.one_ne_top, ENNReal.toReal_one] at hs
    linarith
  · have hCt : ν C ≠ ⊤ := measure_ne_top _ _
    have hr1 : (ν C).toReal < 1 := by
      have := (ENNReal.toReal_lt_toReal hCt ENNReal.one_ne_top).2 hC
      simpa using this
    have hr0 : 0 ≤ (ν C).toReal := ENNReal.toReal_nonneg
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by linarith : (0:ℝ) < 1 - t) hr1
    refine ⟨max N 1, fun n hn => ⟨?_, fun i => ?_⟩⟩
    · have hn0 : 0 < n := by omega
      simp only [Accepted, measureReal_def]
      have hle : κ G * ν C ^ n ≤ 1 := by
        rw [← allTrue_prob κ ν G C hn0]; exact prob_le_one
      rw [someFalse_prob κ ν G C hn0, ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top,
        ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_pow]
      have hk : (κ G).toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by simpa using hG1)
      have hpow : (ν C).toReal ^ n ≤ (ν C).toReal ^ N :=
        pow_le_pow_of_le_one hr0 hr1.le (le_of_max_le_left hn)
      have hk0 : 0 ≤ (κ G).toReal := ENNReal.toReal_nonneg
      have hp0 : 0 ≤ (ν C).toReal ^ n := pow_nonneg hr0 n
      nlinarith
    · simp only [Accepted, measureReal_def, assertion_prob]

/-- Local cross-check posteriors: exact formula bounded by the shared
probability, perfect local detection leaves
only shared risk, truth-independent flags leave the joint unchanged. -/
theorem crossCheckBoundary : CrossCheckBoundary := by
  intro Γ Λ _ _ _ _ _ _ κ _ ν _ G C F n hn hF
  have hFt : ν Fᶜ ≠ ⊤ := measure_ne_top _ _
  have hpow0 : ν Fᶜ ^ n ≠ 0 := pow_ne_zero n hF
  have hpowt : ν Fᶜ ^ n ≠ ⊤ := ENNReal.pow_ne_top hFt
  have hcond : (profile κ ν n)[|noFlag F n] (allTrue G C n) =
      (ν Fᶜ ^ n)⁻¹ * (κ G * ν (C ∩ Fᶜ) ^ n) := by
    rw [cond_apply MeasurableSet.of_discrete, noFlag_prob, inter_comm,
      allTrue_noFlag_prob κ ν G C F hn]
  have hformula : (profile κ ν n)[|noFlag F n] (allTrue G C n) =
      κ G * (ν (C ∩ Fᶜ) / ν Fᶜ) ^ n := by
    rw [hcond, div_eq_mul_inv, mul_pow, ENNReal.inv_pow]; ring
  have hone : ∀ i : Fin n, (profile κ ν n)[|noFlag F n] (assertion G C i) =
      κ G * (ν (C ∩ Fᶜ) / ν Fᶜ) := by
    intro i
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm0 : ν Fᶜ ^ m ≠ 0 := pow_ne_zero m hF
    have hmt : ν Fᶜ ^ m ≠ ⊤ := ENNReal.pow_ne_top hFt
    rw [cond_apply MeasurableSet.of_discrete, noFlag_prob, noFlag_assertion_prob,
      pow_succ, ENNReal.mul_inv (Or.inl hm0) (Or.inl hmt), div_eq_mul_inv]
    calc (ν Fᶜ ^ m)⁻¹ * (ν Fᶜ)⁻¹ * (κ G * ν (C ∩ Fᶜ) * ν Fᶜ ^ m)
        = ((ν Fᶜ ^ m)⁻¹ * ν Fᶜ ^ m) * (κ G * (ν (C ∩ Fᶜ) * (ν Fᶜ)⁻¹)) := by ring
      _ = κ G * (ν (C ∩ Fᶜ) * (ν Fᶜ)⁻¹) := by
        rw [ENNReal.inv_mul_cancel hm0 hmt, one_mul]
  refine ⟨hformula, ?_, hone, fun (hFC : F = Cᶜ) => ?_,
    fun (hind : ν (C ∩ Fᶜ) = ν C * ν Fᶜ) => ?_⟩
  · have hratio : ν (C ∩ Fᶜ) / ν Fᶜ ≤ 1 :=
      ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono inter_subset_right)
    rw [hformula]
    exact mul_le_of_le_one_right' (pow_le_one' hratio n)
  · have hCF : C ∩ Fᶜ = Fᶜ := by rw [hFC, compl_compl, inter_self]
    have hall : (profile κ ν n)[|noFlag F n] (allTrue G C n) = κ G := by
      rw [hcond, hCF, mul_comm (κ G), ← mul_assoc, ENNReal.inv_mul_cancel hpow0 hpowt,
        one_mul]
    have hpos : profile κ ν n (noFlag F n) ≠ 0 := by rw [noFlag_prob]; exact hpow0
    have := cond_isProbabilityMeasure (μ := profile κ ν n) hpos
    have hsome : (profile κ ν n)[|noFlag F n] (someFalse G C n) = 1 - κ G := by
      rw [someFalse_eq, measure_compl MeasurableSet.of_discrete (measure_ne_top _ _),
        measure_univ, hall]
    refine ⟨hall, hsome, fun t ht i ⟨ha, hs⟩ => ?_⟩
    have hG1 : κ G ≤ 1 := prob_le_one
    simp only [Accepted, measureReal_def] at ha hs
    rw [hone, hCF, ENNReal.div_self hF hFt, mul_one] at ha
    rw [hsome, ENNReal.toReal_sub_of_le hG1 ENNReal.one_ne_top, ENNReal.toReal_one] at hs
    linarith
  · rw [hcond, hind, mul_pow, allTrue_prob κ ν G C hn, mul_comm (κ G),
      ← mul_assoc, ← mul_assoc, mul_comm _ (ν C ^ n), mul_assoc (ν C ^ n),
      ENNReal.inv_mul_cancel hpow0 hpowt, mul_one, mul_comm]

/-- Inconsistency eliminates at every world; a survivor follows only with the
explicit coverage premise, and the two-world control refutes it without one. -/
theorem eliminationCoverage : EliminationCoverage := by
  refine ⟨fun World Claim S W hW w hm => hW ⟨w, hm⟩, ?_, ?_⟩
  · intro World Claim ι S W actual k ⟨j, hj⟩ hrest
    by_cases hjk : j = k
    · exact hjk ▸ hj
    · exact absurd ⟨actual, hj⟩ (hrest j hjk)
  · refine ⟨fun b => if b then deniesDuty else fun _ => True, ?_, ?_, ?_, ?_⟩
    · rintro ⟨w, hw⟩
      have h1 := hw true trivial
      have h2 := hw false trivial
      simp [twoWorldSemantics] at h1 h2
      rw [h1] at h2; exact absurd h2 (by decide)
    · exact ⟨false, fun p hp => by simp [deniesDuty] at hp; subst hp; rfl⟩
    · intro hm
      have := hm false (by simp [deniesDuty])
      simp [twoWorldSemantics] at this
    · rintro ⟨j, hj⟩
      cases j
      · have := hj false trivial
        simp [twoWorldSemantics] at this
      · have := hj false (by simp [deniesDuty])
        simp [twoWorldSemantics] at this

end TruthCore.Results.Logic.PrefaceConnectivity
