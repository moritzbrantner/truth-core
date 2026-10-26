import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaMaximumSchema
namespace TruthCore.Results.Logic.MaximumOrderSchema
open TruthCore.Logic.MaximumOrder
theorem maximumOrderSchema : MaximumOrderSchema := by
  intro α _ S hRaise m hm
  exact S.maximal_has_no_distinct_cause hRaise hm

theorem maximumNeedNotCauseOthers : MaximumNeedNotCauseOthers := by
  refine ⟨⟨fun _ _ => False⟩, ?_, ?_, id⟩
  · intro c x hne hc
    exact hc.elim
  · exact ⟨Set.mem_univ true, fun _ _ => Bool.le_true _⟩

theorem causalAscentNeeded : CausalAscentNeeded := by
  refine ⟨⟨fun c x => c = false ∧ x = true⟩, ?_, rfl, rfl⟩
  exact isMax_iff_forall_not_lt.mpr (fun c h => by cases c <;> simp_all)


open TruthCore.Latin.Aquinas.SummaTheologiae
theorem fourthWayMaximumSchemaInstances : FourthWayMaximumSchemaInstances := by
  intro Being Respect _ InAct MoreIn CausesIn esse bonum verum hCause r _ hScale m hm
  exact (perfectionOrderSystem CausesIn r).maximal_has_no_distinct_cause
    (hScale.causesRaiseDegree hCause) ((hScale.isMaximumIn_iff_isMax m).mp hm)

theorem attributionMaximumSchemaInstance : AttributionMaximumSchemaInstance := by
  intro Being Respect Degree _ InAct MoreIn CausesIn r near p hApproach hAll hCause m hm
  letI : Preorder Being := Preorder.lift near
  have hScale : HomogeneousScaleReading InAct MoreIn r := hApproach.homogeneousLift hAll
  exact (perfectionOrderSystem CausesIn r).maximal_has_no_distinct_cause
    (hScale.causesRaiseDegree hCause) ((hScale.isMaximumIn_iff_isMax m).mp hm)


/-- Even a nonempty totally ordered scale with strict comparisons need not
have a maximal member. The empty causal relation would satisfy ascent. -/
theorem maximumNeedNotExist : ¬ ∃ m : Nat, IsMax m := by
  rintro ⟨m, hm⟩
  exact (isMax_iff_forall_not_lt.mp hm) (m + 1) (Nat.lt_succ_self m)

/-- Tied degrees in a preorder preserve maximality of distinct beings. -/
theorem maximumNeedNotBeUnique : MaximumNeedNotBeUnique := by
  refine ⟨false, true, Bool.false_ne_true, ?_, ?_⟩
  · intro b _
    exact le_refl ()
  · intro b _
    exact le_refl ()

end TruthCore.Results.Logic.MaximumOrderSchema
