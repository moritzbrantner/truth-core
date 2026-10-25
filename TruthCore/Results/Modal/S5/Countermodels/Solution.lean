import TruthCore.Modal.S5Research
import TruthCore.Results.Modal.K.ScopeBoundary.Solution
import TruthCore.Results.Modal.K.Laws.Solution
namespace TruthCore.Results.Modal.S5.Countermodels
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite
open TruthCore.Modal.S5Research
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Modern.Hume.Conceivability (StrongBridge Contingent)

private theorem disconnected_s5 : S5Frame disconnected.frame := by
  constructor
  · intro w
    cases w <;> rfl
  · intro w v z hwv hwz
    cases w <;> cases v <;> cases z <;>
      first | exact rfl | exact Bool.noConfusion hwv | exact Bool.noConfusion hwz

private theorem root_collapse : MC disconnected.frame allPredicates .root := by
  intro P _ hp v hv
  cases v with
  | root => exact hp
  | left => exact Bool.noConfusion hv
  | right => exact Bool.noConfusion hv

private theorem root_necessary : Box disconnected.frame (MC disconnected.frame allPredicates) .root := by
  intro v hv
  cases v with
  | root => exact root_collapse
  | left => exact Bool.noConfusion hv
  | right => exact Bool.noConfusion hv

private theorem left_not_collapse : ¬ MC disconnected.frame allPredicates .left := by
  intro h
  have he := identity_separates disconnected.frame allPredicates .left trivial h .right rfl
  exact World.noConfusion he

private theorem disconnected_not_universal : ¬ Universal disconnected.frame := by
  intro h
  exact Bool.noConfusion (h .root .left)

private theorem duplicate_full_failure : ¬ MC duplicates.frame allPredicates false := by
  intro h
  have he := identity_separates duplicates.frame allPredicates false trivial h true rfl
  exact Bool.noConfusion he

private theorem duplicate_separation_missing :
    ¬ expressible duplicates.frame duplicates.valuation (fun w => w = true) := by
  rintro ⟨p, he⟩
  have ht : Holds duplicates.frame duplicates.valuation true p := (congrFun he true).mp rfl
  have hf := (duplicates_constant p).mpr ht
  have bad : (false : Bool) = true := (congrFun he false).mpr hf
  exact Bool.noConfusion bad

private theorem pair_contingent : Contingent pair.frame pairP false := by
  exact ⟨⟨true, rfl, rfl⟩, ⟨false, rfl, Bool.noConfusion⟩⟩

private theorem bridge_failure : ¬ StrongBridge pair.frame indiscriminateC false := by
  intro h
  obtain ⟨v, _, hf⟩ := h (fun _ => False) trivial
  exact hf

private theorem singleton_collapse : MC singleton.frame allPredicates () := by
  intro P _ hp v _
  cases v
  exact hp

private theorem singleton_bridge : StrongBridge singleton.frame witnessedC () := by
  intro P hp
  exact ⟨(), rfl, hp⟩

theorem checks : Countermodels := by
  refine ⟨disconnected_s5, root_collapse, ⟨.root, rfl, root_collapse⟩,
    root_necessary, left_not_collapse, disconnected_not_universal, ?_, ?_, ?_,
    duplicate_language_collapse, duplicate_full_failure, duplicate_not_extensional,
    ?_, duplicate_separation_missing, ?_, ?_, pair_contingent, ?_, ?_, trivial,
    bridge_failure, ?_, ?_, singleton_bridge, singleton_collapse, ?_,
    ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · exact World.noConfusion
  · exact ⟨fun _ => rfl, fun _ _ _ _ _ => rfl⟩
  · intro _ _; rfl
  · exact ⟨⟨true, rfl, rfl⟩, ⟨false, rfl, Bool.noConfusion⟩⟩
  · exact ⟨fun _ => rfl, fun _ _ _ _ _ => rfl⟩
  · intro _ _; rfl
  · intro _ h; exact h.elim
  · intro h; exact h
  · exact ⟨fun _ => rfl, fun _ _ _ _ _ => rfl⟩
  · intro _ _; rfl
  · intro P
    exact TruthCore.Results.Modal.K.Laws.no_contingency singleton.frame () P singleton_collapse
  · intro P _ _ _ hv; exact Bool.noConfusion hv
  · intro _ hv; exact Bool.noConfusion hv
  · rintro ⟨v, hv, _⟩; exact Bool.noConfusion hv
  · intro h; exact Bool.noConfusion (h.1 ())
end TruthCore.Results.Modal.S5.Countermodels
