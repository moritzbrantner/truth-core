import TruthCore.Models.FiniteSupport
import TruthCore.Isabelle.AFP.GoedelGod
import TruthCore.Results.Isabelle.GoedelGod.InvariantFilterMakesNecessaryExistenceUniversal.Solution
import TruthCore.Results.Isabelle.GoedelGod.NecessaryExistenceWorldIsolation.Solution
import TruthCore.Results.Isabelle.GoedelGod.BooleanFragmentClosed.Solution
import TruthCore.Results.Isabelle.GoedelGod.BooleanFragmentStableBearerNE.Solution

/-! Named finite interpretations and closed certificates for #414.
Registration tests formal consequence only; it does not establish metaphysical possibility.
Existing Challenges and proof obligations are unchanged. -/
namespace TruthCore.Models.Scott
open TruthCore.Isabelle.AFP.GoedelGod
namespace OneWorld
def model : TruthCore.Modal.Frame Unit := ⟨fun _ _ => True⟩
def positivity : Positivity Unit Unit := fun Φ w => Φ () w
theorem evaluation0 : @TruthCore.Isabelle.AFP.GoedelGod.NegationPositiveExcludesPositive (Unit) (Unit) (TruthCore.Models.Scott.OneWorld.positivity) := by intro _ Φ hNeg hPos; exact hNeg hPos

theorem evaluation1 : @TruthCore.Isabelle.AFP.GoedelGod.NonPositiveHasPositiveNegation (Unit) (Unit) (TruthCore.Models.Scott.OneWorld.positivity) := by intro _ Φ hNotPos; exact hNotPos

theorem evaluation2 : @TruthCore.Isabelle.AFP.GoedelGod.PositiveClosedUnderNecessaryImplication (Unit) (Unit) (TruthCore.Models.Scott.OneWorld.model) (TruthCore.Models.Scott.OneWorld.positivity) := by intro w Φ Ψ hPos hBox; exact hBox w trivial () hPos

theorem evaluation3 : @TruthCore.Isabelle.AFP.GoedelGod.GodLikePositive (Unit) (Unit) (TruthCore.Models.Scott.OneWorld.positivity) := by intro _ Φ hPos; exact hPos

theorem evaluation4 : @TruthCore.Isabelle.AFP.GoedelGod.PositiveNecessarilyPositive (Unit) (Unit) (TruthCore.Models.Scott.OneWorld.model) (TruthCore.Models.Scott.OneWorld.positivity) := by
  intro w Φ hPos v _
  cases v; cases w; exact hPos

theorem evaluation5 : @TruthCore.Isabelle.AFP.GoedelGod.NecessaryExistence (Unit) (Unit) (TruthCore.Models.Scott.OneWorld.model) (Unit.unit) (Unit.unit) := by
  intro Φ hEssence v _
  cases v; exact ⟨(), hEssence.1⟩

theorem evaluation6 : @TruthCore.Isabelle.AFP.GoedelGod.NecessaryExistencePositive (Unit) (Unit) (TruthCore.Models.Scott.OneWorld.model) (TruthCore.Models.Scott.OneWorld.positivity) := by
  intro w
  cases w
  exact evaluation5

theorem evaluation7 : @TruthCore.Isabelle.AFP.GoedelGod.GodLikeNecessarilyExists (Unit) (Unit) (TruthCore.Models.Scott.OneWorld.model) (TruthCore.Models.Scott.OneWorld.positivity) := by intro _ _ _; exact ⟨(), fun _ hp => hp⟩

end OneWorld
namespace FixedPositivity
def model : TruthCore.Modal.Frame Bool := ⟨fun _ _ => True⟩
def positivity : Positivity Bool Unit := fun Φ _ => Φ () false
theorem evaluation0 : @TruthCore.Isabelle.AFP.GoedelGod.NegationPositiveExcludesPositive (Bool) (Unit) (TruthCore.Models.Scott.FixedPositivity.positivity) := by intro _ Φ hNeg hPos; exact hNeg hPos

theorem evaluation1 : @TruthCore.Isabelle.AFP.GoedelGod.NonPositiveHasPositiveNegation (Bool) (Unit) (TruthCore.Models.Scott.FixedPositivity.positivity) := by intro _ Φ hNotPos; exact hNotPos

theorem evaluation2 : @TruthCore.Isabelle.AFP.GoedelGod.PositiveClosedUnderNecessaryImplication (Bool) (Unit) (TruthCore.Models.Scott.FixedPositivity.model) (TruthCore.Models.Scott.FixedPositivity.positivity) := by intro w Φ Ψ hPos hBox; exact hBox false trivial () hPos

theorem evaluation3 : @TruthCore.Isabelle.AFP.GoedelGod.GodLikePositive (Bool) (Unit) (TruthCore.Models.Scott.FixedPositivity.positivity) := by intro _ Φ hPos; exact hPos

theorem evaluation4 : @TruthCore.Isabelle.AFP.GoedelGod.PositiveNecessarilyPositive (Bool) (Unit) (TruthCore.Models.Scott.FixedPositivity.model) (TruthCore.Models.Scott.FixedPositivity.positivity) := by
  intro w Φ hPos v _
  exact hPos

theorem evaluation5 : ¬ (@TruthCore.Isabelle.AFP.GoedelGod.NecessaryExistence (Bool) (Unit) (TruthCore.Models.Scott.FixedPositivity.model) (Unit.unit) (false)) := by
  intro hNE
  have hEss : Essence model (fun _ v => v = false) () false := by
    constructor
    · rfl
    · intro Ψ hΨ v _ y hΦ
      cases v with
      | false => cases y; exact hΨ
      | true => exact Bool.noConfusion hΦ
  obtain ⟨y, hy⟩ := hNE (fun _ v => v = false) hEss true trivial
  exact Bool.noConfusion hy

theorem evaluation6 : ¬ (@TruthCore.Isabelle.AFP.GoedelGod.NecessaryExistencePositive (Bool) (Unit) (TruthCore.Models.Scott.FixedPositivity.model) (TruthCore.Models.Scott.FixedPositivity.positivity)) := by
  intro h
  exact evaluation5 (h false)

theorem evaluation7 : ¬ (@TruthCore.Isabelle.AFP.GoedelGod.GodLikeNecessarilyExists (Bool) (Unit) (TruthCore.Models.Scott.FixedPositivity.model) (TruthCore.Models.Scott.FixedPositivity.positivity)) := by
  intro h
  obtain ⟨x, hx⟩ := h false true trivial
  exact Bool.noConfusion (hx (fun _ v => v = false) rfl)

end FixedPositivity
namespace InvariantFilter
def model : TruthCore.Modal.Frame Bool := ⟨fun _ _ => True⟩
theorem evaluation0 : @TruthCore.Isabelle.AFP.GoedelGod.FilteredNecessaryExistence (Bool) (Unit) (TruthCore.Models.Scott.InvariantFilter.model) (TruthCore.Isabelle.AFP.GoedelGod.WorldInvariantProperty) (Unit.unit) (false) := by
  exact TruthCore.Results.Isabelle.GoedelGod.InvariantFilterMakesNecessaryExistenceUniversal.checks model () false

theorem evaluation1 : ¬ (@TruthCore.Isabelle.AFP.GoedelGod.NecessaryExistence (Bool) (Unit) (TruthCore.Models.Scott.InvariantFilter.model) (Unit.unit) (false)) := by
  intro h
  have isolated := (TruthCore.Results.Isabelle.GoedelGod.NecessaryExistenceWorldIsolation.checks model () false).mp h
  exact Bool.noConfusion (isolated true trivial)

end InvariantFilter
namespace BooleanStable
def model : TruthCore.Modal.Frame Bool := ⟨fun _ _ => True⟩
def atom : Bool → Bool → Bool := fun x w => !(x && w)
def admissible := BooleanGeneratedProperty atom
theorem evaluation0 : @TruthCore.Isabelle.AFP.GoedelGod.FilteredNecessaryExistence (Bool) (Bool) (TruthCore.Models.Scott.BooleanStable.model) (TruthCore.Models.Scott.BooleanStable.admissible) (false) (false) := by
  let F := model
  have hAtomAdmissible :
      BooleanGeneratedProperty atom (fun x w => atom x w = true) :=
    (TruthCore.Results.Isabelle.GoedelGod.BooleanFragmentClosed.checks (World := Bool) (Ind := Bool) atom).1
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
    TruthCore.Results.Isabelle.GoedelGod.BooleanFragmentStableBearerNE.checks F atom false hStable false
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
    have hIsolated := (TruthCore.Results.Isabelle.GoedelGod.NecessaryExistenceWorldIsolation.checks F false false).mp hNecessary
    have hImpossible : true = false := hIsolated true trivial
    cases hImpossible
  exact hYes

theorem evaluation1 : ¬ (@TruthCore.Isabelle.AFP.GoedelGod.NecessaryExistence (Bool) (Bool) (TruthCore.Models.Scott.BooleanStable.model) (false) (false)) := by
  intro h
  have isolated := (TruthCore.Results.Isabelle.GoedelGod.NecessaryExistenceWorldIsolation.checks model false false).mp h
  exact Bool.noConfusion (isolated true trivial)

end BooleanStable
namespace BooleanUnstable
def model : TruthCore.Modal.Frame Bool := ⟨fun _ _ => True⟩
def atom : Bool → Bool → Bool := fun x w => !(x && w)
def admissible := BooleanGeneratedProperty atom
theorem evaluation0 : ¬ (@TruthCore.Isabelle.AFP.GoedelGod.FilteredNecessaryExistence (Bool) (Bool) (TruthCore.Models.Scott.BooleanUnstable.model) (TruthCore.Models.Scott.BooleanUnstable.admissible) (true) (true)) := by
  let F := model
  have hAtomAdmissible :
      BooleanGeneratedProperty atom (fun x w => atom x w = true) :=
    (TruthCore.Results.Isabelle.GoedelGod.BooleanFragmentClosed.checks (World := Bool) (Ind := Bool) atom).1
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
    TruthCore.Results.Isabelle.GoedelGod.BooleanFragmentStableBearerNE.checks F atom false hStable false
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
    have hIsolated := (TruthCore.Results.Isabelle.GoedelGod.NecessaryExistenceWorldIsolation.checks F false false).mp hNecessary
    have hImpossible : true = false := hIsolated true trivial
    cases hImpossible
  exact hNo

theorem evaluation1 : ¬ (@TruthCore.Isabelle.AFP.GoedelGod.NecessaryExistence (Bool) (Bool) (TruthCore.Models.Scott.BooleanUnstable.model) (true) (true)) := by
  intro h
  have isolated := (TruthCore.Results.Isabelle.GoedelGod.NecessaryExistenceWorldIsolation.checks model true true).mp h
  exact Bool.noConfusion (isolated false trivial)

end BooleanUnstable
end TruthCore.Models.Scott
