module
public import TruthCore.Modal.PossibleImpossibility
@[expose] public section
namespace TruthCore.Results.Modal.PossibleImpossibility
open TruthCore.Modal
open TruthCore.Modal.PossibleImpossibility
open TruthCore.Modal.NecessaryIfExistent
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)
theorem conditionalDuality : TruthCore.Modal.PossibleImpossibility.Certificate := by
  intro W F P w logic
  constructor
  · intro input possible v accessible
    apply logic v accessible
    intro absent
    have impossible : ImpossibleExistence F P v := by
      intro x vx px
      exact absent ⟨x, vx, px⟩
    have actual := input ⟨v, accessible, impossible⟩
    obtain ⟨x, wx, px⟩ := possible
    exact actual x wx px
  · intro stable possibleImpossible x wx px
    obtain ⟨v, wv, impossible⟩ := possibleImpossible
    obtain ⟨y, vy, py⟩ := stable ⟨x, wx, px⟩ v wv
    exact impossible y vy py
theorem controls : TruthCore.Modal.PossibleImpossibility.Controls := by
  dsimp [TruthCore.Modal.PossibleImpossibility.Controls, Input, Stable,
    ImpossibleExistence, universal, ascending, Box, Dia]
  constructor
  · exact ⟨(by intro h; obtain ⟨v, _, hv⟩ := h; exact False.elim (hv false trivial trivial)),
      ⟨false, trivial, trivial⟩, (by intro _ v _; exact ⟨false, trivial, trivial⟩)⟩
  constructor
  · constructor
    · intro h
      obtain ⟨v, _, hv⟩ := h
      exact False.elim (hv true (Or.inr rfl) trivial)
    constructor
    · intro h
      have impossible := h ⟨true, Or.inl rfl, by intro x hx eq; cases hx with
        | inl bad => cases bad
        | inr eqTrue => cases eq.symm.trans eqTrue⟩
      exact impossible false (Or.inl rfl) rfl
    · intro h
      obtain ⟨x, hx, eq⟩ := h ⟨false, Or.inl rfl, rfl⟩ true (Or.inl rfl)
      cases hx with
      | inl bad => cases bad
      | inr eqTrue => cases eq.symm.trans eqTrue
  constructor
  · intro h
    apply h False
    intro impossible
    obtain ⟨v, _, hv⟩ := impossible
    exact False.elim (hv false trivial trivial)
  · exact ⟨trivial, by intro h; exact h false trivial trivial⟩
end TruthCore.Results.Modal.PossibleImpossibility
