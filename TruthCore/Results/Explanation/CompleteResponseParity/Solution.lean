import TruthCore.Explanation.CompleteResponseParity
import TruthCore.Results.Explanation.JointCooperation.Solution

namespace TruthCore.Results.Explanation.CompleteResponseParity
open TruthCore.Explanation.CompleteResponseParity
open TruthCore.Explanation.JointCooperation
open TruthCore.Causality.JointGroups TruthCore.Causality.DerivativeJointPower
open TruthCore.Results.Explanation.JointCooperation
open TruthCore.Results.Explanation.UltimateAdequacy
set_option autoImplicit false

/-- The three observables agree at EVERY scenario, not just at the actual one. -/
theorem matched_observations : MatchedObservations := by
  intro s
  rcases s with ⟨a, b⟩
  cases a <;> cases b <;> decide

theorem completed_actual (e : SingleEvent) :
    completedSingle.occurs completedSingle.actual e := by
  cases e <;> first | rfl | exact ⟨rfl, rfl⟩

theorem completed_coherent : completedSingle.coherent :=
  ⟨trivial, fun _ _ => ⟨trivial, fun e _ => completed_actual e, completed_actual _⟩⟩

/-- The new root-to-a and root-to-b records satisfy the SAME scenario-wide
sufficiency requirement already imposed on the two-contributor effect record. -/
theorem completed_sufficient (g : SingleGroup) : completedSingle.jointlySufficient g := by
  intro s _ ho
  cases g with
  | ra => exact (ho .r (Or.inl rfl)).1
  | rb => exact (ho .r (Or.inl rfl)).2
  | ab => exact ⟨ho .a (Or.inl (Or.inl rfl)), ho .b (Or.inl (Or.inr rfl))⟩

theorem complete_profiles : CompleteProfiles :=
  ⟨⟨completed_coherent, completed_sufficient⟩,
   ⟨(background .plural).1, (background .plural).2.1⟩⟩

/-- Both a and b remain independently removable from the target group, as in
the original single control. This is about scenarios, not possible worlds. -/
theorem completed_needed : Needed completedSingle .ab .a .b := by
  constructor
  · refine ⟨Or.inl rfl, fun h => ?_⟩
    have hh := h (false, true) trivial (fun e he => by
      rcases he with ⟨he | he, hne⟩ | he
      · exact (hne he).elim
      · subst he; rfl
      · exact he.elim)
    exact Bool.noConfusion hh.1
  · refine ⟨Or.inr rfl, fun h => ?_⟩
    have hh := h (true, false) trivial (fun e he => by
      rcases he with ⟨he | he, hne⟩ | he
      · subst he; rfl
      · exact (hne he).elim
      · exact he.elim)
    exact Bool.noConfusion hh.2

/-- The single hidden root really is a *scenario-sufficient* common ancestor,
not just a member of a projected graph. -/
theorem completed_common_source : CommonSource completedSingle .a .b := by
  refine ⟨.r, completed_actual .r, ?_, ?_, ?_, ?_⟩
  · apply Relation.TransGen.single
    change single.exercisedGroups.graph.edge .r .a
    exact single_edge .ra .r rfl
  · apply Relation.TransGen.single
    change single.exercisedGroups.graph.edge .r .b
    exact single_edge .rb .r rfl
  · intro s _ ho
    exact (ho .r rfl).1
  · intro s _ ho
    exact (ho .r rfl).2

theorem root_parity : RootParity := by
  have hLeast : least single.exercisedGroups.graph .r := by
    rcases single_brute_ctl with ⟨_, _, _, _, h, _, _, _, _⟩
    exact h
  constructor
  · change least single.exercisedGroups.graph .r
    exact hLeast
  · exact plural_no_least

theorem cooperation_parity : CooperationParity :=
  ⟨completed_needed, plural_needed, completed_common_source, plural_brute.2.2⟩

theorem supply_parity : SupplyParity := by
  have hSingle : ∀ e, Supply single.groups singleIntrinsic e := by
    rcases single_brute_ctl with ⟨_, _, _, _, _, _, _, _, h⟩
    exact h
  exact ⟨hSingle, plural_supply⟩

/-- In #744 `single` the root occurs even when a does not. Thus the original
single-root control did NOT satisfy sufficiency of its root-to-a record. -/
theorem original_gap : OriginalGap := by
  intro h
  have bad := h (false, true) trivial (fun e he => by
    rcases he with he | he
    · have hr : e = SingleEvent.r := he
      subst e
      trivial
    · exact he.elim)
  exact Bool.noConfusion bad

theorem certificate : TruthCore.Explanation.CompleteResponseParity.Certificate :=
  ⟨matched_observations, complete_profiles, root_parity,
   cooperation_parity, supply_parity, original_gap⟩

end TruthCore.Results.Explanation.CompleteResponseParity
