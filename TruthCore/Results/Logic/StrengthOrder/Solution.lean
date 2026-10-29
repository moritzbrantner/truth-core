import TruthCore.Logic.Strength.Order
namespace TruthCore.Results.Logic.StrengthOrder
open TruthCore.Logic.Strength.Order
universe u

theorem implication {α : Type u} [LinearOrder α] (x y : α) (hS : Strict x y) : Weak x y :=
  le_of_lt hS

theorem deltaForward {α : Type u} [LinearOrder α] (x y : α) (hS : Strict x y) : Unequal x y :=
  ne_of_gt hS

theorem reconstruction {α : Type u} [LinearOrder α] (x y : α) (hW : Weak x y) (hD : Unequal x y) : Strict x y :=
  lt_of_le_of_ne hW (Ne.symm hD)

theorem equivalence : ExactDelta := by
  intro α _ x y
  exact ⟨fun h => ⟨implication x y h, deltaForward x y h⟩,
    fun h => reconstruction x y h.1 h.2⟩

theorem allowedCases : AllowedCasesLaw := by
  intro α _ x y
  exact le_iff_lt_or_eq.trans (or_congr Iff.rfl eq_comm)

theorem remainderIdentity : RemainderLaw := by
  intro α _ x y
  constructor
  · intro h
    exact ⟨le_of_eq h.symm, fun hl => (ne_of_gt hl) h⟩
  · rintro ⟨hW, hNot⟩
    rcases (allowedCases α x y).1 hW with hS | hEq
    · exact False.elim (hNot hS)
    · exact hEq

theorem separator : ZeroSeparates := by
  exact ⟨True.intro, Nat.le_refl 0, Nat.lt_irrefl 0⟩
end TruthCore.Results.Logic.StrengthOrder
