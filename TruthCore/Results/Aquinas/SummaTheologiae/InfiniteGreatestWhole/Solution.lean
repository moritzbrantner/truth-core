import TruthCore.Models.InfiniteGreatestWhole
namespace TruthCore.Results.Aquinas.SummaTheologiae.InfiniteGreatestWhole
open TruthCore.Models.InfiniteGreatestWhole
open TruthCore.Latin.Aquinas.SummaTheologiae

private theorem point_ne : origin ≠ unitPoint := by
  intro h
  have h0 := congrFun h 0
  norm_num [origin, unitPoint] at h0

private theorem left_not_subset : ¬ leftRegion ⊆ rightRegion := by
  intro h
  have := h (show origin ∈ leftRegion from Set.mem_singleton _)
  exact point_ne (Set.mem_singleton_iff.mp this)

private theorem right_not_subset : ¬ rightRegion ⊆ leftRegion := by
  intro h
  have := h (show unitPoint ∈ rightRegion from Set.mem_singleton _)
  exact point_ne (Set.mem_singleton_iff.mp this).symm

private theorem whole_maximal : IsMaximalIn inAct moreIn () whole := by
  refine ⟨trivial, ?_⟩
  intro s hs
  exact hs.2 (Set.subset_univ s)

private theorem region_control : RegionControl := by
  have hinj : Function.Injective (fun r : ℝ => (fun _ : Fin 3 => r)) := by
    intro r s h
    exact congrFun h 0
  have hNotBounded : ¬ BddAbove (coordinates whole) := by
    rintro ⟨a, ha⟩
    have h : a + 1 ≤ a := ha ⟨(fun _ => a + 1), trivial, rfl⟩
    linarith
  have hProper : leftRegion ≠ whole := by
    intro h
    have : unitPoint ∈ leftRegion := h ▸ Set.mem_univ _
    exact point_ne (Set.mem_singleton_iff.mp this).symm
  refine ⟨⟨trivial, fun _ _ => Set.subset_univ _⟩,
    Set.infinite_of_injective_forall_mem hinj (fun _ => trivial),
    ?_, ⟨whole, fun _ _ => Set.subset_univ _⟩, hNotBounded,
    ⟨fun _ => trivial, fun _ _ => Iff.rfl⟩, whole_maximal, ?_,
    (fun _ _ h => h), ?_, ?_, ?_⟩
  · apply Set.infinite_of_injective_forall_mem
      (f := fun r : ℝ => ({fun _ : Fin 3 => r} : Region))
    · intro r s h
      exact hinj (Set.singleton_injective h)
    · intro _
      trivial
  · intro h
    obtain ⟨s, hs⟩ := h whole
    exact whole_maximal.2 s hs
  · intro h
    exact h leftRegion hProper trivial
  · intro h
    exact h whole whole_maximal leftRegion hProper trivial
  · intro s hs heq
    exact hNotBounded (heq ▸ hs)

private theorem interval_control : OpenIntervalControl := by
  have hExtend : QuartaViaNoMaximalDegree openMore () := by
    intro x
    refine ⟨⟨(x.val + 1) / 2, ?_⟩, ?_⟩
    · constructor <;> linarith [x.property.1, x.property.2]
    · change x.val < (x.val + 1) / 2
      linarith [x.property.2]
  refine ⟨isLUB_Ioo (show (0 : ℝ) < 1 by norm_num), ?_,
    ⟨1, fun _ h => h.2.le⟩, hExtend, ?_⟩
  · simp
  · rintro ⟨m, hm⟩
    obtain ⟨n, hn⟩ := hExtend m
    exact (isMax_iff_forall_not_lt.mp hm) n hn

private theorem incomparable_control : IncomparableControl := by
  have hne : leftRegion ≠ rightRegion := fun h => left_not_subset h.subset
  refine ⟨hne, ?_, ?_, ?_, ?_⟩
  · refine ⟨by simp, ?_⟩
    intro s hs hle
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact le_rfl
    · exact (left_not_subset hle).elim
  · refine ⟨by simp, ?_⟩
    intro s hs hle
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact (right_not_subset hle).elim
    · exact le_rfl
  · intro h
    exact right_not_subset (h.2 (by simp))
  · intro h
    exact left_not_subset (h.2 (by simp))

/-- New geometry/interval controls, composed with the exact previously proved
finite-top/Nat joint witnesses. No geometric relation becomes causality. -/
theorem checks : Certificate :=
  ⟨region_control, interval_control, incomparable_control,
    TruthCore.Models.QuartaViaDegreeFork.branchWitnesses⟩
end TruthCore.Results.Aquinas.SummaTheologiae.InfiniteGreatestWhole
