import TruthCore.Results.Isabelle.GoedelGod.BooleanFragmentClosed.Solution
import TruthCore.Results.Isabelle.GoedelGod.BooleanFragmentStableBearerNE.Solution
import TruthCore.Results.Isabelle.GoedelGod.NecessaryExistenceWorldIsolation.Solution

namespace TruthCore.Results.Isabelle.GoedelGod.BooleanFragmentNontrivialModel

open TruthCore.Modal
open TruthCore.Isabelle.AFP.GoedelGod

/-- The primitive is true everywhere except for individual `true` in world
`true`. Its four Boolean readouts do not name an arbitrary individual or
world, but the primitive itself remains an ungrounded stipulation. -/
theorem checks : BooleanFragmentNontrivialModel := by
  let F : Frame Bool := ⟨fun _ _ => True⟩
  let atom : Bool → Bool → Bool := fun x w => !(x && w)
  have hAtomAdmissible :
      BooleanGeneratedProperty atom (fun x w => atom x w = true) :=
    (BooleanFragmentClosed.checks (World := Bool) (Ind := Bool) atom).1
  have hNonInvariant :
      ∃ Φ, BooleanGeneratedProperty atom Φ ∧ ¬ WorldInvariantProperty Φ := by
    refine ⟨fun x w => atom x w = true, hAtomAdmissible, ?_⟩
    intro hInvariant
    have hFalse : atom true true = true :=
      (hInvariant true false true).mp (by decide)
    change false = true at hFalse
    cases hFalse
  have hNoWorldName :
      ¬ BooleanGeneratedProperty atom (fun _ w => w = false) := by
    rintro ⟨readout, hReadout⟩
    have hAtFalse : readout true = true := by
      exact (hReadout false false).mp rfl
    have hImpossible : true = false :=
      (hReadout false true).mpr hAtFalse
    cases hImpossible
  have hNoIndividualName :
      ¬ BooleanGeneratedProperty atom (fun x _ => x = false) := by
    rintro ⟨readout, hReadout⟩
    have hAtFalse : readout true = true := by
      exact (hReadout false false).mp rfl
    have hImpossible : true = false :=
      (hReadout true false).mpr hAtFalse
    cases hImpossible
  have hStable : ∀ w next, atom false w = atom false next := by
    intro w next
    cases w <;> cases next <;> decide
  have hYes : FilteredNecessaryExistence F (BooleanGeneratedProperty atom) false false :=
    BooleanFragmentStableBearerNE.checks F atom false hStable false
  let Φ : Property Bool Bool := fun x w => atom x w = false
  have hΦAdmissible : BooleanGeneratedProperty atom Φ := by
    refine ⟨fun bit => !bit, ?_⟩
    intro x w
    change (atom x w = false) ↔ (!atom x w) = true
    cases atom x w <;> decide
  have hEssence : FilteredEssence F (BooleanGeneratedProperty atom) Φ true true := by
    constructor
    · decide
    · intro Ψ _ hΨ next _ y hAt
      cases next <;> cases y
      · change true = false at hAt
        cases hAt
      · change true = false at hAt
        cases hAt
      · change true = false at hAt
        cases hAt
      · exact hΨ
  have hNo : ¬ FilteredNecessaryExistence F (BooleanGeneratedProperty atom) true true := by
    intro hNecessary
    have hExample : ∃ y : Bool, Φ y false :=
      hNecessary Φ hΦAdmissible hEssence false trivial
    obtain ⟨y, hy⟩ := hExample
    cases y
    · change true = false at hy
      cases hy
    · change true = false at hy
      cases hy
  have hNotScott : ¬ NecessaryExistence F false false := by
    intro hNecessary
    have hIsolated := (NecessaryExistenceWorldIsolation.checks F false false).mp hNecessary
    have hImpossible : true = false := hIsolated true trivial
    cases hImpossible
  exact ⟨F, atom, (fun _ _ => trivial), hNonInvariant, hNoWorldName,
    hNoIndividualName, hYes, hNo, hNotScott⟩

end TruthCore.Results.Isabelle.GoedelGod.BooleanFragmentNontrivialModel
