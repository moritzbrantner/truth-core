import TruthCore.Modal.S5Research
namespace TruthCore.Results.Modal.S5.DomainBoundary
open TruthCore.Modal TruthCore.Modal.ResearchFixture TruthCore.Modal.S5Research
open TruthCore.Isabelle.AFP.GoedelGod (Dia)
private theorem atom_collapse : MC pair.frame atomOnly false := by
  rintro P ⟨i, rfl⟩ hp
  exact Bool.noConfusion hp
private theorem atom_not_collapse : ¬ MC pair.frame atomOnly true := by
  intro h
  have hf := h pairP ⟨(), rfl⟩ rfl false rfl
  exact Bool.noConfusion hf
private theorem atom_extensional : PropositionalExtensionality atomOnly := by
  intro w v h
  cases w with
  | false =>
    cases v with
    | false => rfl
    | true => exact Bool.noConfusion ((h pairP ⟨(), rfl⟩).mpr rfl)
  | true =>
    cases v with
    | false => exact Bool.noConfusion ((h pairP ⟨(), rfl⟩).mp rfl)
    | true => rfl
private theorem not_negation : ¬ atomOnly (fun v => ¬ pairP v) := by
  rintro ⟨i, he⟩
  have hn : ¬ pairP false := Bool.noConfusion
  have bad : pairP false := (congrFun he false).mp hn
  exact Bool.noConfusion bad

theorem checks : DomainBoundary := by
  exact ⟨⟨fun _ => rfl, fun _ _ _ _ _ => rfl⟩, fun _ _ => rfl,
    atom_extensional, atom_collapse, ⟨false, rfl, atom_collapse⟩,
    atom_not_collapse, ⟨⟨true, rfl, rfl⟩, ⟨false, rfl, Bool.noConfusion⟩⟩,
    ⟨(), rfl⟩, not_negation⟩
end TruthCore.Results.Modal.S5.DomainBoundary
