import Mathlib.Order.Bounds.Basic

/-! A maximum-in-an-order schema (#412). `IsMax` means maximal, not greatest.
The order and the causal relation are separate data. A cause raises degree only
under the explicit `CausesRaiseDegree` condition. No existence, uniqueness,
causality of a maximum, or identification with God is built into this schema. -/
namespace TruthCore.Logic.MaximumOrder

/-- A causal relation on one ordered domain. Stipulative schema interface;
`causes c x` means the chosen cause-of-degree relation, not arbitrary causation. -/
structure System (α : Type) where
  causes : α → α → Prop

/-- Every distinct cause is strictly higher than its effect in the chosen order.
This is an additional condition on a system, not a consequence of ordering. -/
def System.CausesRaiseDegree {α : Type} [Preorder α] (S : System α) : Prop :=
  ∀ c x, c ≠ x → S.causes c x → x < c

/-- A maximal member has no distinct cause when causes strictly raise degree.
Self-causation is outside this statement. Mathlib's preorder admits tied grades. -/
theorem System.maximal_has_no_distinct_cause {α : Type} [Preorder α]
    {S : System α} (hRaise : S.CausesRaiseDegree) {m : α} (hm : IsMax m) :
    ∀ c, c ≠ m → ¬ S.causes c m := by
  intro c hne hc
  exact (isMax_iff_forall_not_lt.mp hm) c (hRaise c m hne hc)

/-- Advertised schema: the causal ascent condition is inside the quantified
conditional, so verifying the schema does not establish any causal premise. -/
def MaximumOrderSchema : Prop :=
  ∀ (α : Type) [Preorder α] (S : System α), S.CausesRaiseDegree →
    ∀ m, IsMax m → ∀ c, c ≠ m → ¬ S.causes c m

/-- A control with an actual greatest member and a lower member, causal ascent
and no causal edges. Thus maximum + ascent does not imply causing all others. -/
def MaximumNeedNotCauseOthers : Prop :=
  ∃ (S : System Bool), S.CausesRaiseDegree ∧ IsGreatest Set.univ true ∧
    ¬ S.causes true false

/-- Dropping causal ascent permits a distinct cause of a maximum. -/
def CausalAscentNeeded : Prop :=
  ∃ (S : System Bool), IsMax true ∧ S.causes false true

/-- A preorder can have distinct maximal members tied at one degree. -/
def MaximumNeedNotBeUnique : Prop :=
  letI : Preorder Bool := Preorder.lift (fun _ : Bool => ())
  ∃ a b : Bool, a ≠ b ∧ IsMax a ∧ IsMax b

end TruthCore.Logic.MaximumOrder
