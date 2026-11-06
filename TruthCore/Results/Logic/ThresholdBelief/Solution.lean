module

public import TruthCore.Logic.ThresholdBelief
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section
namespace TruthCore.Results.Logic.ThresholdBelief
open TruthCore.Logic.ThresholdBelief
open MeasureTheory Set
open scoped ENNReal

variable {Ω : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

private theorem measurable (A : Set Ω) : MeasurableSet A := (Set.toFinite A).measurableSet

/-- The core is determined by genuine singleton probability, not a stipulated
belief implication or a separate consistency assumption. -/
theorem coreMembership (t : ℝ) (x : Ω) :
    x ∈ HeavyCore μ t ↔ ∀ A, Accepted μ t A → x ∈ A := by
  constructor
  · intro hx A hA
    by_contra hnot
    have hsub : A ⊆ ({x}ᶜ : Set Ω) := by
      intro y hy hxy
      have : y=x := by simpa using hxy
      subst y
      exact hnot hy
    have hle := measureReal_mono (μ := μ) hsub
    have hcomp := measureReal_compl (μ := μ) (measurable ({x} : Set Ω))
    simp only [probReal_univ] at hcomp
    dsimp [HeavyCore] at hx
    dsimp [Accepted] at hA
    linarith
  · intro h
    by_contra hn
    have hm : μ.real {x} ≤ 1-t := le_of_not_gt hn
    have hcomp := measureReal_compl (μ := μ) (measurable ({x} : Set Ω))
    simp only [probReal_univ] at hcomp
    have ha : Accepted μ t ({x}ᶜ) := by dsimp [Accepted]; linarith
    exact (h ({x}ᶜ) ha) (by simp)

omit [Fintype Ω] [MeasurableSingletonClass Ω] in
private theorem accepted_intersections (t : ℝ) (ht : t≤1)
    (hc : ConjunctionClosed μ t) {I : Type} (s : Finset I) (A : I → Set Ω)
    (ha : ∀ i ∈ s, Accepted μ t (A i)) : Accepted μ t (⋂ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [Accepted] using ht
  | @insert i s hi ih =>
    rw [Finset.set_biInter_insert]
    exact hc _ _ (ha i (Finset.mem_insert_self i s))
      (ih fun j hj => ha j (Finset.mem_insert_of_mem hj))

theorem coreClosed (t : ℝ) (ht : t≤1) :
    ConjunctionClosed μ t ↔ Accepted μ t (HeavyCore μ t) := by
  classical
  constructor
  · intro hc
    let S : Finset (Set Ω) := Finset.univ.filter (Accepted μ t)
    have ha : Accepted μ t (⋂ A ∈ S, A) :=
      accepted_intersections μ t ht hc S id fun A hA => (Finset.mem_filter.mp hA).2
    have heq : (⋂ A ∈ S, A) = HeavyCore μ t := by
      ext x
      simp only [Set.mem_iInter]
      constructor
      · intro hx
        exact (coreMembership μ t x).mpr fun A hA =>
          hx A (Finset.mem_filter.mpr ⟨Finset.mem_univ A, hA⟩)
      · intro hx A hA
        exact (coreMembership μ t x).mp hx A (Finset.mem_filter.mp hA).2
    exact heq ▸ ha
  · intro hcore A B hA hB
    have hsub : HeavyCore μ t ⊆ A ∩ B := by
      intro x hx
      exact ⟨(coreMembership μ t x).mp hx A hA,
        (coreMembership μ t x).mp hx B hB⟩
    exact hcore.trans (measureReal_mono (μ := μ) hsub)

theorem core : CoreBoundary := by
  intro Ω _ _ _ μ _ t ht0 ht1
  refine ⟨coreMembership μ t, coreClosed μ t ht1, ?_, ?_⟩
  · simpa [Accepted] using ht1
  · simpa [Accepted] using not_le.mpr ht0

theorem uniformSingleton (N : ℕ) (i : Fin N) :
    (uniform N).real {i} = 1/(N:ℝ) := by
  simp [uniform, Measure.real, ProbabilityTheory.uniformOn_univ]

private theorem uniform_probability (N : ℕ) (hN : 0<N) :
    IsProbabilityMeasure (uniform N) := by
  let : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  unfold uniform
  infer_instance

theorem uniformClosed (N : ℕ) (hN : 0<N) (t : ℝ) (ht0 : 0<t) (ht1 : t≤1) :
    ConjunctionClosed (uniform N) t ↔ 1-1/(N:ℝ)<t := by
  let := uniform_probability N hN
  rw [coreClosed (uniform N) t ht1]
  constructor
  · intro ha
    by_contra hn
    have he : HeavyCore (uniform N) t = ∅ := by
      ext x
      simp only [HeavyCore, mem_ofPred_eq, uniformSingleton, mem_empty_iff_false, iff_false]
      intro hx
      linarith
    rw [he] at ha
    have : t≤0 := by simpa [Accepted] using ha
    linarith
  · intro h
    have he : HeavyCore (uniform N) t = univ := by
      ext x
      simp only [HeavyCore, mem_ofPred_eq, uniformSingleton, mem_univ, iff_true]
      linarith
    rw [he]
    simpa [Accepted] using ht1

theorem uniformBoundary : UniformBoundary := by
  refine ⟨uniformClosed, ?_⟩
  intro t ht0 ht1
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt (sub_pos.mpr ht1)
  let N := m+2
  have hN : 0<N := by omega
  have hN2 : 2≤N := by omega
  have hden : 1/((N:ℕ):ℝ) ≤ 1/((m:ℝ)+1) := by
    apply one_div_le_one_div_of_le (by positivity)
    dsimp [N]
    push_cast
    linarith
  have hloss : t ≤ 1-1/(N:ℝ) := by linarith
  refine ⟨N,hN2,?_,?_,?_⟩
  · intro hc
    have := (uniformClosed N hN t ht0 (le_of_lt ht1)).mp hc
    linarith
  · intro i
    let := uniform_probability N hN
    dsimp [Accepted]
    rw [measureReal_compl (measurable ({i} : Set (Fin N))), probReal_univ, uniformSingleton]
    exact hloss
  · ext x
    simp only [mem_iInter, mem_compl_iff, mem_singleton_iff, mem_empty_iff_false, iff_false]
    intro h
    exact h x rfl

private theorem intersectionBound (A B : Set Ω) :
    μ.real A + μ.real B ≤ 1 + μ.real (A ∩ B) := by
  have h := measureReal_union_add_inter (μ := μ) (measurable B)
  have hu : μ.real (A ∪ B) ≤ 1 := by
    simpa only [probReal_univ] using measureReal_mono (μ := μ) (subset_univ (A ∪ B))
  linarith

private theorem finiteSupport {I : Type} (s : Finset I) (A : I → Set Ω) :
    1 ≤ μ.real (⋂ i ∈ s, A i) + s.sum (fun i => 1-μ.real (A i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.set_biInter_insert, Finset.sum_insert hi]
    have h := intersectionBound μ (A i) (⋂ j ∈ s, A j)
    linarith

theorem support : SupportBoundary := by
  constructor
  · intro Ω _ _ _ μ _ I _ A
    simpa using finiteSupport μ Finset.univ A
  · intro Ω _ _ _ μ _ A B hA hB
    dsimp [Accepted] at *
    have h := intersectionBound μ A B
    linarith

private theorem skew_probability : IsProbabilityMeasure skew := by
  constructor
  norm_num [skew, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply']
  rw [← one_div (20 : ℝ≥0∞), ← ENNReal.add_div]
  norm_num only [show (19 : ℝ≥0∞)+1 = 20 from by norm_num]
  exact ENNReal.div_self (by norm_num) (by norm_num)

private theorem skewTrue : skew.real {true} = 19/20 := by
  norm_num [skew, Measure.real, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply',
    ENNReal.toReal_div]

private theorem skewFalse : skew.real {false} = 1/20 := by
  norm_num [skew, Measure.real, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply',
    ENNReal.toReal_div]

theorem skewSurvivor : SkewSurvivor := by
  let := skew_probability
  have hcore : HeavyCore skew (9/10) = {true} := by
    ext b
    cases b <;> norm_num [HeavyCore, skewFalse, skewTrue]
  have haccept : Accepted skew (9/10) {true} := by
    dsimp [Accepted]
    rw [skewTrue]
    norm_num
  refine ⟨skew_probability, skewTrue, skewFalse, ?_, haccept, ?_, ?_, by simp⟩
  · exact (coreClosed skew (9/10) (by norm_num)).mpr (hcore ▸ haccept)
  · norm_num [Accepted]
  · rw [skewFalse]; norm_num

end TruthCore.Results.Logic.ThresholdBelief
