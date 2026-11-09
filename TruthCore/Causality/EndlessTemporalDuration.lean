module

public import Mathlib.Data.Nat.Basic

/-! ETERNAL_2: future-unending temporal presence, allowing a beginning.
The supplied preorder gives a strict earlier-than relation. Neither totality,
convex support, ambient-time coverage nor changing life-states is required.
Applicability of this order and presence interpretation remains open. -/

@[expose] public section
namespace TruthCore.Causality.EndlessTemporalDuration

universe u

/-- Nonempty temporal presence with no final present moment. This is ordinary
succession of distinct ordered moments, not inequality of a subject's states.
A beginning is allowed. The order dictionary is explicit framework scope. -/
def FutureUnending {Time : Type u} [Preorder Time] (present : Time → Prop) : Prop :=
  (∃ t, present t) ∧ ∀ t, present t → ∃ later, t < later ∧ present later

/-- Empty presence cannot certify duration, even on an empty timeline. -/
theorem emptyFails {Time : Type u} [Preorder Time] :
    ¬ FutureUnending (fun _ : Time => False) := by
  intro ⟨⟨_, h⟩, _⟩
  exact h

/-- Any supplied final present moment defeats the definition. No global
maximum or total order assumption is needed. -/
theorem endpointFails {Time : Type u} [Preorder Time] (present : Time → Prop)
    (last : Time) (hLast : present last)
    (hFinal : ∀ t, present t → ¬ last < t) : ¬ FutureUnending present := by
  intro h
  obtain ⟨t, hlt, ht⟩ := h.2 last hLast
  exact hFinal t ht hlt

/-- Nonvacuity with an actual first moment: ordinary Nat time suffices. -/
example : FutureUnending (fun _ : Nat => True) := by
  exact ⟨⟨0, trivial⟩, fun t _ => ⟨t + 1, Nat.lt_succ_self t, trivial⟩⟩

/-- A finite, nonempty temporal extent fails at its endpoint. -/
example : ¬ FutureUnending (fun t : Nat => t ≤ 2) := by
  apply endpointFails _ 2 (by decide)
  intro t ht hlt
  exact Nat.not_lt_of_ge ht hlt

/-- There is no requirement for past-unboundedness. -/
example : ¬ ∃ t : Nat, t < 0 := by
  intro ⟨t, h⟩
  exact Nat.not_lt_zero t h

/-- Constant states are compatible with unending succession of moments. -/
example : FutureUnending (fun _ : Nat => True) ∧
    ∀ s t : Nat, (fun _ : Nat => ()) s = (fun _ : Nat => ()) t := by
  exact ⟨⟨⟨0, trivial⟩, fun t _ => ⟨t + 1, Nat.lt_succ_self t, trivial⟩⟩,
    fun _ _ => rfl⟩

end TruthCore.Causality.EndlessTemporalDuration
