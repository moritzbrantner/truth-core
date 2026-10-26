import Mathlib.Order.Fin.Basic
import TruthCore.Models.FiniteSupport
import TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionCauseMoreSuch.Solution

/-! Named finite interpretations and closed certificates for #414.
Registration tests formal consequence only; it does not establish metaphysical possibility.
Existing Challenges and proof obligations are unchanged. -/
namespace TruthCore.Models.OrderSecondary
open TruthCore.Latin.Aquinas.SummaTheologiae
abbrev B := TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionCauseMoreSuch.B
namespace B
abbrev p := TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionCauseMoreSuch.B.p
abbrev a := TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionCauseMoreSuch.B.a
abbrev b := TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionCauseMoreSuch.B.b
end B
abbrev Degree := Fin 3
abbrev finiteOrder : Preorder Degree where
  le a b := a.val ≤ b.val
  lt a b := a.val < b.val
  le_refl := by decide
  le_trans := by decide
  lt_iff_le_not_ge := by decide
abbrev order : Preorder Degree := finiteOrder
def d0 : Degree := ⟨0, by decide⟩
def d1 : Degree := ⟨1, by decide⟩
def d2 : Degree := ⟨2, by decide⟩
def near : B → Degree | .p => d2 | .b => d1 | .a => d0
def inAct : B → Unit → Prop := fun _ _ => True
def moreIn : Unit → B → B → Prop := fun _ x y => near y < near x
def causes : B → B → Unit → Prop
  | .p, .p, _ => False | .p, .a, _ => True | .p, .b, _ => True
  | .a, .p, _ => False | .a, .a, _ => False | .a, .b, _ => True
  | .b, .p, _ => False | .b, .a, _ => False | .b, .b, _ => False
def creature : B → Prop := fun x => x ≠ B.p
def model := (inAct, moreIn, causes, creature, near)
theorem sameDegreeOrder : ∀ x y : B, near x < near y ↔ TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionCauseMoreSuch.near x < TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionCauseMoreSuch.near y := by intro x y; cases x <;> cases y <;> decide
instance {p : B → Prop} [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p B.p ∧ p B.a ∧ p B.b)
    ⟨fun h x => by cases x; exact h.1; exact h.2.1; exact h.2.2, fun h => ⟨h B.p, h B.a, h B.b⟩⟩
theorem enumerateBeing : ∀ x : B, x = TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionCauseMoreSuch.B.p ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionCauseMoreSuch.B.a ∨ x = TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionCauseMoreSuch.B.b := by
  intro x; cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inr rfl | rfl

theorem enumerateDegree : ∀ x : Degree, x = d0 ∨ x = d1 ∨ x = d2 := by decide
theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.ApproachToPrimaryReading (TruthCore.Models.OrderSecondary.B) (Unit) (TruthCore.Models.OrderSecondary.Degree) (TruthCore.Models.OrderSecondary.order) (TruthCore.Models.OrderSecondary.inAct) (TruthCore.Models.OrderSecondary.moreIn) (Unit.unit) (TruthCore.Models.OrderSecondary.near) (TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionCauseMoreSuch.B.p) := by exact ⟨trivial, fun _ _ => Iff.rfl⟩

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading (TruthCore.Models.OrderSecondary.B) (TruthCore.Models.OrderSecondary.Degree) (TruthCore.Models.OrderSecondary.order) (TruthCore.Models.OrderSecondary.near) (TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionCauseMoreSuch.B.p) := by
  intro x hx
  cases x
  · exact absurd rfl hx
  · exact (show (0 : Nat) < 2 by decide)
  · exact (show (1 : Nat) < 2 by decide)

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.OrderedToPrimaryAsCauseReading (TruthCore.Models.OrderSecondary.B) (Unit) (TruthCore.Models.OrderSecondary.inAct) (TruthCore.Models.OrderSecondary.causes) (TruthCore.Models.OrderSecondary.creature) (Unit.unit) (TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionCauseMoreSuch.B.p) := by intro x hx _; cases x; exact absurd rfl hx; trivial; trivial

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading (TruthCore.Models.OrderSecondary.B) (TruthCore.Models.OrderSecondary.creature) (TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionCauseMoreSuch.B.p) := by intro _ hx; exact hx

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInGenusCausesAllInGenusReading (TruthCore.Models.OrderSecondary.B) (Unit) (TruthCore.Models.OrderSecondary.inAct) (TruthCore.Models.OrderSecondary.moreIn) (TruthCore.Models.OrderSecondary.causes) := by
  intro r m hm x hx _
  cases m with
  | p => cases x; exact absurd rfl hx; trivial; trivial
  | a => exact absurd (show near B.a < near B.p by decide) (hm.2 B.p)
  | b => exact absurd (show near B.b < near B.p by decide) (hm.2 B.p)

theorem evaluation5 : ¬ (@TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading (TruthCore.Models.OrderSecondary.B) (Unit) (TruthCore.Models.OrderSecondary.causes) (TruthCore.Models.OrderSecondary.moreIn)) := by
  intro h
  have bad := h B.a B.b () (by decide) trivial
  exact absurd bad (by change ¬ (near B.b < near B.a); decide)

end TruthCore.Models.OrderSecondary
