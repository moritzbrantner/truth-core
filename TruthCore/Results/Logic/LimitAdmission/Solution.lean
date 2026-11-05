module

public import TruthCore.Logic.LimitAdmission
public import TruthCore.Results.Case.Catholicism.StageOne.FinitePopulationCoverControls.Solution
public import TruthCore.Results.Causality.SupertaskStableEndpoint.Solution
public import TruthCore.Results.Causality.SupertaskOscillation.Solution

/-! Conditional mathematics and explicit omission controls for #486.
No physical or modal applicability premise is discharged. -/

@[expose] public section
namespace TruthCore.Results.Logic.LimitAdmission
open Filter Topology
open TruthCore.Logic.LimitAdmission
open TruthCore.Causality
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual

/-- A nonempty sequence filter forces ambient closure membership. Closedness
and containment then suffice for membership in the chosen admissible set. -/
theorem closureLaws : ClosureLaws := by
  intro X _ f x h
  constructor
  · exact mem_closure_of_tendsto h (Eventually.of_forall fun n => Set.mem_range_self n)
  · intro A hclosed hstages
    exact hclosed.mem_of_tendsto h (Eventually.of_forall fun n => hstages (Set.mem_range_self n))

/-- Coordinatewise convergence in the Mathlib product topology, with each
fixed candidate absent after its own index. No uniform empty stage is used. -/
theorem tail_tendsto : Tendsto tailProfile atTop (𝓝 falseProfile) := by
  apply tendsto_pi_nhds.mpr
  intro b
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (b + 1)] with n hn
  simp [tailProfile, falseProfile, show ¬ n ≤ b by omega]

theorem false_not_tail : falseProfile ∉ tailWorlds := by
  rintro ⟨n, hn⟩
  have h := congrFun hn n
  simp [tailProfile, falseProfile] at h

/-- Modal closedness is retained as a hypothesis, never inferred from finite
omission or from a frame's accessibility relation. -/
theorem modalTransfer : ModalTransfer := by
  intro W hclosed hW
  exact (closureLaws (ℕ → Bool) tailProfile falseProfile tail_tendsto).2 W hclosed hW

theorem modalBoundary : ModalBoundary := by
  have hc : falseProfile ∈ closure tailWorlds :=
    (closureLaws (ℕ → Bool) tailProfile falseProfile tail_tendsto).1
  refine ⟨TruthCore.Results.Case.Catholicism.StageOne.FinitePopulationCoverControls.checks,
    ?_, ?_, tail_tendsto, hc, false_not_tail, ?_, isClosed_closure, hc⟩
  · intro n b
    simp [tailProfile, finiteCoverTailPresent]
  · intro xs
    refine ⟨xs.foldr Nat.max 0 + 1, ?_⟩
    intro b hb
    have hle : b ≤ xs.foldr Nat.max 0 := by
      induction xs with
      | nil => simp at hb
      | cons a xs ih =>
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact Nat.le_max_left _ _
        · exact Nat.le_trans (ih hb) (Nat.le_max_right _ _)
    simp [tailProfile, show ¬ xs.foldr Nat.max 0 + 1 ≤ b by omega]
  · intro hclosed
    exact false_not_tail (modalTransfer tailWorlds hclosed (Set.Subset.refl _))

theorem event_tendsto : Tendsto eventTime atTop (𝓝 (0 : ℝ)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem event_pos (n : ℕ) : 0 < eventTime n := by
  unfold eventTime
  positivity

theorem zero_not_event : (0 : ℝ) ∉ eventTimes := by
  rintro ⟨n, hn⟩
  exact (ne_of_gt (event_pos n)) hn

/-- A temporal occurrence policy, separate from the modal world policy. -/
theorem temporalTransfer : TemporalTransfer := by
  intro E hclosed hE
  exact (closureLaws ℝ eventTime 0 event_tendsto).2 E hclosed hE

theorem temporalBoundary : TemporalBoundary := by
  have hc : (0 : ℝ) ∈ closure eventTimes := (closureLaws ℝ eventTime 0 event_tendsto).1
  refine ⟨event_tendsto, ?_, ?_, hc, zero_not_event, ?_, ?_, isClosed_closure, hc⟩
  · intro n
    refine ⟨event_pos n, ?_⟩
    unfold eventTime
    apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  · exact ⟨⟨le_rfl, by norm_num⟩, fun _ hx => hx.1⟩
  · rintro t ⟨n, rfl⟩
    refine ⟨eventTime (n + 1), Set.mem_range_self _, ?_⟩
    unfold eventTime
    apply one_div_lt_one_div_of_lt (by positivity)
    push_cast
    linarith
  · intro hclosed
    exact zero_not_event (temporalTransfer eventTimes hclosed (Set.Subset.refl _))

theorem stage_tendsto : Tendsto stageTime atTop (𝓝 (1 : ℝ)) := by
  change Tendsto (fun n => 1 - eventTime n) atTop (𝓝 (1 : ℝ))
  simpa only [sub_zero] using tendsto_const_nhds.sub event_tendsto

theorem stage_lt (n : ℕ) : stageTime n < 1 := by
  have h := event_pos n
  unfold stageTime
  linarith

theorem one_not_stage : (1 : ℝ) ∉ stageEvents := by
  rintro ⟨n, hn⟩
  exact (ne_of_lt (stage_lt n)) hn

/-- For discrete Bool, topological convergence coincides with the existing
stable-output predicate; this equivalence is proved, not substituted for limits. -/
theorem bool_tendsto_iff (output : ℕ → Bool) (b : Bool) :
    Tendsto output atTop (𝓝 b) ↔ StableAtLimit output b := by
  rw [nhds_discrete, tendsto_pure]
  exact eventually_atTop

theorem supertaskTransfer : SupertaskTransfer := by
  constructor
  · intro E hclosed hE
    exact (closureLaws ℝ stageTime 1 stage_tendsto).2 E hclosed hE
  · intro state b hb hterminal
    exact tendsto_nhds_unique hterminal hb

theorem supertaskBoundary : SupertaskBoundary := by
  have hc : (1 : ℝ) ∈ closure stageEvents := (closureLaws ℝ stageTime 1 stage_tendsto).1
  refine ⟨TruthCore.Results.Causality.SupertaskStableEndpoint.supertaskStableEndpoint,
    stage_tendsto, ?_, ?_, ?_, ?_, hc, one_not_stage, ?_, ⟨isClosed_closure, hc⟩, ?_,
    tendsto_const_nhds, ?_, tendsto_const_nhds⟩
  · intro n m hnm
    have h : eventTime m < eventTime n := by
      unfold eventTime
      apply one_div_lt_one_div_of_lt (by positivity)
      exact_mod_cast (Nat.add_lt_add_right hnm 1)
    unfold stageTime
    linarith
  · rintro ⟨n, hn⟩
    exact SupertaskMoment.noConfusion hn
  · intro n
    refine ⟨?_, stage_lt n⟩
    have h := temporalBoundary.2.1 n
    unfold stageTime
    linarith [h.2]
  · exact stage_lt
  · intro hclosed
    exact one_not_stage (supertaskTransfer.1 stageEvents hclosed (Set.Subset.refl _))
  · intro b hb
    exact TruthCore.Results.Causality.SupertaskOscillation.supertaskOscillation b
      ((bool_tendsto_iff _ _).mp hb)
  · intro hterminal
    have h : (false : Bool) = true := tendsto_nhds_unique hterminal tendsto_const_nhds
    exact Bool.noConfusion h

/-- Explicitly premise-bound form of the sufficient bridge. None of its
three domain inputs is asserted for an actual metaphysical interpretation. -/
theorem closedAdmission {X : Type} [TopologicalSpace X] (f : ℕ → X) (x : X) (A : Set X)
    (hconverges : Converges f x) (hclosed : ClosedAdmission A)
    (hstages : StagesAdmitted f A) : LimitAdmitted x A :=
  (closureLaws X f x hconverges).2 A hclosed hstages

/-- The package certifies separate domain applications and omission controls. -/
theorem checks : Package :=
  ⟨closureLaws, modalTransfer, temporalTransfer, supertaskTransfer,
    modalBoundary, temporalBoundary, supertaskBoundary⟩

end TruthCore.Results.Logic.LimitAdmission
