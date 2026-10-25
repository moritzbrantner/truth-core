import TruthCore.Results.Modal.S4.Countermodels.Solution
namespace TruthCore.Results.Modal.S4.ScopeBoundary
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite
open TruthCore.Modal.S4Research
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)

theorem pair_constant (φ : Formula Bool) :
    Holds (pockets true).frame (pockets true).valuation .right φ ↔
    Holds (pockets true).frame (pockets true).valuation .twin φ := by
  induction φ with
  | atom a => cases a <;> rfl
  | falsum => rfl
  | imp p q hp hq =>
    exact ⟨fun h ht => hq.mp (h (hp.mpr ht)), fun h ht => hq.mpr (h (hp.mp ht))⟩
  | box _ _ => rfl
  | diamond _ _ => rfl

theorem right_language : MC (pockets true).frame (language true) .right := by
  rintro P ⟨φ, rfl⟩ hp v hv
  cases v with
  | root => cases hv
  | left => cases hv
  | right => exact hp
  | twin => exact (pair_constant φ).mp hp

theorem twin_language : MC (pockets true).frame (language true) .twin := by
  rintro P ⟨φ, rfl⟩ hp v hv
  cases v with
  | root => cases hv
  | left => cases hv
  | right => exact (pair_constant φ).mpr hp
  | twin => exact hp

theorem right_not_full : ¬ MC (pockets true).frame allPredicates .right := by
  intro h
  have he := (K.Laws.full_iff_successors _ _).mp h .twin rfl
  cases he

theorem twin_not_full : ¬ MC (pockets true).frame allPredicates .twin := by
  intro h
  have he := (K.Laws.full_iff_successors _ _).mp h .right rfl
  cases he

theorem right_no_possible_full : ¬ Dia (pockets true).frame
    (MC (pockets true).frame allPredicates) .right := by
  rintro ⟨v, hv, hm⟩
  cases v with
  | root => cases hv
  | left => cases hv
  | right => exact right_not_full hm
  | twin => exact twin_not_full hm

theorem language_box_possible : Box (pockets true).frame (fun w =>
    Dia (pockets true).frame (MC (pockets true).frame (language true)) w) .root := by
  intro v _
  cases v with
  | root => exact ⟨.left, rfl, Countermodels.left_collapse true (language true)⟩
  | left => exact ⟨.left, rfl, Countermodels.left_collapse true (language true)⟩
  | right => exact ⟨.right, rfl, right_language⟩
  | twin => exact ⟨.twin, rfl, twin_language⟩

theorem not_language_extensional : ¬ PropositionalExtensionality (language true) := by
  intro h
  have he := h .right .twin (by rintro P ⟨φ, rfl⟩; exact pair_constant φ)
  cases he

theorem checks : ScopeBoundary := by
  refine ⟨⟨rfl, rfl⟩, ?_, right_not_full, right_language, twin_language,
    ?_, language_box_possible, not_language_extensional, rfl, rfl, rfl, rfl⟩
  · intro h; cases h
  · intro h; exact right_no_possible_full (h .right rfl)
end TruthCore.Results.Modal.S4.ScopeBoundary
