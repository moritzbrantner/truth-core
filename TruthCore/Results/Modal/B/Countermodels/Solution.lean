import TruthCore.Modal.BResearch
import TruthCore.Results.Modal.K.Laws.Solution
namespace TruthCore.Results.Modal.B.Countermodels
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite
open TruthCore.Modal.BResearch
open TruthCore.Isabelle.AFP.GoedelGod (Box)

theorem reflexive_chain : Reflexive chain.frame := by
  intro w; cases w <;> rfl

theorem symmetric_chain : Symmetric chain.frame := by
  intro w v h; cases w <;> cases v <;> exact h

theorem not_transitive_chain : ¬ Transitive chain.frame := by
  intro h
  exact Bool.noConfusion (h .left .middle .right rfl rfl)

theorem no_full (w : World) : ¬ MC chain.frame allPredicates w := by
  intro h
  have hs := (K.Laws.full_iff_successors chain.frame w).mp h
  cases w with
  | left => cases hs .middle rfl
  | middle => cases hs .right rfl
  | right => cases hs .middle rfl

theorem box_p_left : Box chain.frame p .left := by
  intro v hv
  cases v with
  | left => rfl
  | middle => rfl
  | right => cases hv

theorem not_box_p_middle : ¬ Box chain.frame p .middle := by
  intro h; exact Bool.noConfusion (h .right rfl)

theorem no_language (w : World) : ¬ MC chain.frame language w := by
  intro h
  cases w with
  | left =>
    have hb := h (Box chain.frame p) ⟨.box (.atom ()), rfl⟩ box_p_left .middle rfl
    exact not_box_p_middle hb
  | middle =>
    have hf := h p ⟨.atom (), rfl⟩ rfl .right rfl
    exact Bool.noConfusion hf
  | right =>
    have hn : ¬ p .right := by intro hf; exact Bool.noConfusion hf
    exact h (fun w => ¬ p w) ⟨.neg (.atom ()), rfl⟩ hn .middle rfl rfl

theorem atom_left : MC chain.frame atomsOnly .left := by
  rintro P ⟨i, rfl⟩ _ v hv
  cases v with
  | left => rfl
  | middle => rfl
  | right => cases hv

theorem atom_not_middle : ¬ MC chain.frame atomsOnly .middle := by
  intro h
  exact Bool.noConfusion (h p ⟨(), rfl⟩ rfl .right rfl)

theorem not_box_closed : ¬ ∀ P, atomsOnly P → atomsOnly (Box chain.frame P) := by
  intro h
  obtain ⟨i, he⟩ := h p ⟨(), rfl⟩
  have hm : Box chain.frame p .middle := (congrFun he World.middle).mpr rfl
  exact not_box_p_middle hm

theorem checks : Countermodels := by
  refine ⟨reflexive_chain, symmetric_chain, not_transitive_chain, no_full,
    no_language, ?_, atom_left, ⟨.left, rfl, atom_left⟩, atom_not_middle,
    not_box_closed, rfl, rfl, rfl, rfl⟩
  exact ⟨⟨.left, rfl, rfl⟩, ⟨.right, rfl, fun h => Bool.noConfusion h⟩⟩
end TruthCore.Results.Modal.B.Countermodels
