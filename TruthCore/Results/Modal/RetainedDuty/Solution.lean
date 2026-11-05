module
public import TruthCore.Modal.RetainedDuty
@[expose] public section
namespace TruthCore.Results.Modal.RetainedDuty
open TruthCore.Modal.RetainedDuty

theorem directCore (s : Case) (hd : PresentDuty s) (hn : PresentInability s)
    (ho : PresentOIC s) : TruthCore.Logic.ConfigurationFalse := by
  have canReturn : s.able .after .originalReturn := ho .originalReturn hd
  exact hn canReturn
theorem retentionTransfer (s : Case) (hi : InitialDuty s) (hr : Retention s) :
    PresentDuty s := by
  exact hr hi

theorem retainedCore (s : Case) (hi : InitialDuty s) (hr : Retention s)
    (hn : PresentInability s) (ho : PresentOIC s) : TruthCore.Logic.ConfigurationFalse := by
  have duty := retentionTransfer s hi hr
  exact directCore s duty hn ho

theorem controls : Controls := by
  have hlapse : PresentOIC lapse := by
    intro a ha
    exact Stage.noConfusion ha.1
  have hnever : PresentOIC neverOwed := by
    intro a ha
    exact ha.elim
  have habler : PresentOIC ableReturn := by
    intro _ _
    trivial
  have hcrash : ¬ PresentOIC crash := by
    intro h
    exact Stage.noConfusion (h .originalReturn rfl)
  have hfuture : ¬ FutureCan crash .after .originalReturn := by
    rintro ⟨t, ht, ha⟩
    cases t <;> cases ht <;> cases ha
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, futureRepair, ?_⟩
  · exact ⟨fun h => h, fun _ h => h.elim, fun h => h⟩
  · exact ⟨rfl, habler, fun h => h True.intro⟩
  · exact ⟨rfl, Stage.noConfusion, hcrash⟩
  · exact ⟨fun h => h.elim, Stage.noConfusion, hnever, fun h => h⟩
  · exact ⟨⟨rfl, rfl⟩, Stage.noConfusion, hlapse,
      fun h => Stage.noConfusion (h ⟨rfl, rfl⟩).1, ⟨rfl, rfl⟩,
      fun h => Stage.noConfusion h.1⟩
  · exact ⟨rfl, fun h => h, habler⟩
  · exact ⟨rfl, fun h => h, Stage.noConfusion⟩
  · refine ⟨?_, fun h => Stage.noConfusion h.1, fun _ h => h⟩
    intro a ha
    exact ⟨.later, True.intro, rfl, ha⟩
  · exact ⟨⟨rfl, rfl⟩, hfuture, ⟨.later, True.intro, rfl⟩,
      Action.noConfusion, fun h => hfuture (h .originalReturn rfl)⟩
  · exact TruthCore.Results.Modal.DeonticFutureBoundary.certificate

namespace Evaluations
theorem stages (t : Stage) : t = .before ∨ t = .after ∨ t = .later := by
  cases t
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
theorem actions (a : Action) : a = .originalReturn ∨ a = .compensation ∨ a = .debtRepayment := by
  cases a
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
theorem noDuty0 : ¬ (TruthCore.Modal.RetainedDuty.PresentDuty TruthCore.Modal.RetainedDuty.noDuty) := by
  exact fun h => h
theorem noDuty1 : (TruthCore.Modal.RetainedDuty.PresentInability TruthCore.Modal.RetainedDuty.noDuty) := by
  exact fun h => h
theorem noDuty2 : (TruthCore.Modal.RetainedDuty.PresentOIC TruthCore.Modal.RetainedDuty.noDuty) := by
  exact fun _ h => h.elim
theorem noDuty3 : ¬ (TruthCore.Modal.RetainedDuty.InitialDuty TruthCore.Modal.RetainedDuty.noDuty) := by
  exact fun h => h
theorem noDuty4 : (TruthCore.Modal.RetainedDuty.Retention TruthCore.Modal.RetainedDuty.noDuty) := by
  exact fun h => h.elim
theorem ableReturn0 : (TruthCore.Modal.RetainedDuty.PresentDuty TruthCore.Modal.RetainedDuty.ableReturn) := by
  exact rfl
theorem ableReturn1 : ¬ (TruthCore.Modal.RetainedDuty.PresentInability TruthCore.Modal.RetainedDuty.ableReturn) := by
  exact fun h => h True.intro
theorem ableReturn2 : (TruthCore.Modal.RetainedDuty.PresentOIC TruthCore.Modal.RetainedDuty.ableReturn) := by
  exact fun _ _ => True.intro
theorem ableReturn3 : (TruthCore.Modal.RetainedDuty.InitialDuty TruthCore.Modal.RetainedDuty.ableReturn) := by
  exact rfl
theorem ableReturn4 : (TruthCore.Modal.RetainedDuty.Retention TruthCore.Modal.RetainedDuty.ableReturn) := by
  exact fun h => h
theorem crash0 : (TruthCore.Modal.RetainedDuty.PresentDuty TruthCore.Modal.RetainedDuty.crash) := by
  exact rfl
theorem crash1 : (TruthCore.Modal.RetainedDuty.PresentInability TruthCore.Modal.RetainedDuty.crash) := by
  exact Stage.noConfusion
theorem crash2 : ¬ (TruthCore.Modal.RetainedDuty.PresentOIC TruthCore.Modal.RetainedDuty.crash) := by
  exact fun h => Stage.noConfusion (h .originalReturn rfl)
theorem crash3 : (TruthCore.Modal.RetainedDuty.InitialDuty TruthCore.Modal.RetainedDuty.crash) := by
  exact rfl
theorem crash4 : (TruthCore.Modal.RetainedDuty.Retention TruthCore.Modal.RetainedDuty.crash) := by
  exact fun h => h
theorem lapse0 : ¬ (TruthCore.Modal.RetainedDuty.PresentDuty TruthCore.Modal.RetainedDuty.lapse) := by
  exact fun h => Stage.noConfusion h.1
theorem lapse1 : (TruthCore.Modal.RetainedDuty.PresentInability TruthCore.Modal.RetainedDuty.lapse) := by
  exact Stage.noConfusion
theorem lapse2 : (TruthCore.Modal.RetainedDuty.PresentOIC TruthCore.Modal.RetainedDuty.lapse) := by
  exact fun _ h => False.elim (Stage.noConfusion h.1)
theorem lapse3 : (TruthCore.Modal.RetainedDuty.InitialDuty TruthCore.Modal.RetainedDuty.lapse) := by
  exact ⟨rfl, rfl⟩
theorem lapse4 : ¬ (TruthCore.Modal.RetainedDuty.Retention TruthCore.Modal.RetainedDuty.lapse) := by
  exact fun h => Stage.noConfusion (h ⟨rfl, rfl⟩).1
theorem neverOwed0 : ¬ (TruthCore.Modal.RetainedDuty.PresentDuty TruthCore.Modal.RetainedDuty.neverOwed) := by
  exact fun h => h
theorem neverOwed1 : (TruthCore.Modal.RetainedDuty.PresentInability TruthCore.Modal.RetainedDuty.neverOwed) := by
  exact Stage.noConfusion
theorem neverOwed2 : (TruthCore.Modal.RetainedDuty.PresentOIC TruthCore.Modal.RetainedDuty.neverOwed) := by
  exact fun _ h => h.elim
theorem neverOwed3 : ¬ (TruthCore.Modal.RetainedDuty.InitialDuty TruthCore.Modal.RetainedDuty.neverOwed) := by
  exact fun h => h
theorem neverOwed4 : (TruthCore.Modal.RetainedDuty.Retention TruthCore.Modal.RetainedDuty.neverOwed) := by
  exact fun h => h.elim
end Evaluations
theorem branching : BranchControls := by
  have hinterp : ∀ a, debtPlan.current.duty .after a →
      TruthCore.Modal.DeonticFutureBoundary.Ought
        ⟨fun _ b => debtPlan.ideal b⟩ debtPlan.actual
        (fun b => BranchAbility debtPlan b a) := by
    intro a ha b hb
    exact ⟨.later, True.intro, hb, rfl, ha⟩
  refine ⟨branchRepair, branchRepair debtPlan hinterp ⟨.recovery, rfl, True.intro⟩,
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact h
  · rintro ⟨t, _, h⟩
    exact Branch.noConfusion h.1
  · intro t h
    exact Branch.noConfusion h.1
  · intro t a
    exact ⟨fun h => Branch.noConfusion h.1, fun h => h.elim⟩
  · rintro ⟨b, _, t, _, h⟩
    exact Action.noConfusion h.2.2
end TruthCore.Results.Modal.RetainedDuty
