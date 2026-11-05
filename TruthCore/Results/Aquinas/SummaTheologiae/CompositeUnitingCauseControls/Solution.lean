module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7UnitingControl

@[expose] public section

namespace TruthCore.Results.Aquinas.SummaTheologiae.CompositeUnitingCauseControls
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting

/-- Each of the five uniting-cause premises is needed for the derivation of
`CompositeHasAUnitingCauseReading`, and the five are jointly satisfiable with a
composite present. -/
theorem checks : Control.Certificate := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `true` is composite with the single component `false`; nothing causes.
    refine ⟨Bool, Unit, fun x => x = true, fun a x => a = false ∧ x = true,
      fun _ _ _ _ => False, fun _ _ _ => False, fun _ _ _ => False, (), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      obtain ⟨a, b, ha, hb, hab⟩ := h true rfl
      exact hab (ha.1.trans hb.1.symm)
    · intro x hx
      exact ⟨false, ⟨rfl, hx⟩, fun h => Bool.noConfusion (h.trans hx)⟩
    · intro x a b ha hb hab
      exact (hab (ha.1.trans hb.1.symm)).elim
    · intro _ _ _ _ h
      exact h.elim
    · intro _ _ _ _ h
      exact h.elim
    · intro _ _ h
      exact h
    · intro h
      obtain ⟨_, _, hc⟩ := h true rfl
      exact hc
  · -- `true` has components `false` and `true`, but nothing unites them.
    refine ⟨Bool, Unit, fun x => x = true, fun _ x => x = true,
      fun _ _ _ _ => False, fun _ _ _ => False, fun _ _ _ => False, (), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact ⟨false, true, hx, hx, fun h => Bool.noConfusion h⟩
    · intro h
      obtain ⟨_, hc⟩ := h true false true rfl rfl (fun h => Bool.noConfusion h)
      exact hc
    · intro _ _ _ _ h
      exact h.elim
    · intro _ _ _ _ h
      exact h.elim
    · intro _ _ h
      exact h
    · intro h
      obtain ⟨_, _, hc⟩ := h true rfl
      exact hc
  · -- The whole `true` unites itself and causes its own being, not efficiently.
    refine ⟨Bool, Unit, fun x => x = true, fun _ x => x = true,
      fun c _ _ x => c = true ∧ x = true, fun _ _ _ => False,
      fun c x _ => c = true ∧ x = true, (), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact ⟨false, true, hx, hx, fun h => Bool.noConfusion h⟩
    · intro x _ _ hx _ _
      exact ⟨true, rfl, hx⟩
    · intro h
      obtain ⟨_, hr⟩ := h true false true true ⟨rfl, rfl⟩
      exact hr
    · intro _ _ _ _ h
      exact h
    · intro _ _ h
      exact h
    · intro h
      obtain ⟨c, hne, hc, _⟩ := h true rfl
      exact hne hc
  · -- A distinct efficient uniter `false` that causes no being.
    refine ⟨Bool, Unit, fun x => x = true, fun _ x => x = true,
      fun c _ _ x => c = false ∧ x = true, fun c x _ => c = false ∧ x = true,
      fun _ _ _ => False, (), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact ⟨false, true, hx, hx, fun h => Bool.noConfusion h⟩
    · intro x _ _ hx _ _
      exact ⟨false, rfl, hx⟩
    · intro _ _ _ _ h
      exact ⟨(), h⟩
    · intro h
      exact h false false true true ⟨rfl, rfl⟩
    · intro x _ h
      exact Bool.noConfusion (h.1.symm.trans h.2)
    · intro h
      obtain ⟨_, _, hc⟩ := h true rfl
      exact hc
  · -- The whole `true` efficiently unites itself and causes its own being.
    refine ⟨Bool, Unit, fun x => x = true, fun _ x => x = true,
      fun c _ _ x => c = true ∧ x = true, fun c x _ => c = true ∧ x = true,
      fun c x _ => c = true ∧ x = true, (), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact ⟨false, true, hx, hx, fun h => Bool.noConfusion h⟩
    · intro x _ _ hx _ _
      exact ⟨true, rfl, hx⟩
    · intro _ _ _ _ h
      exact ⟨(), h⟩
    · intro _ _ _ _ h
      exact h
    · intro h
      exact h true () ⟨rfl, rfl⟩
    · intro h
      obtain ⟨c, hne, hc, _⟩ := h true rfl
      exact hne hc
  · -- A distinct efficient uniter `false` that causes the being of `true`.
    refine ⟨Bool, Unit, fun x => x = true, fun _ x => x = true,
      fun c _ _ x => c = false ∧ x = true, fun c x _ => c = false ∧ x = true,
      fun c x _ => c = false ∧ x = true, (), ?_, ?_, ?_, ?_, ?_, ⟨true, rfl⟩⟩
    · intro x hx
      exact ⟨false, true, hx, hx, fun h => Bool.noConfusion h⟩
    · intro x _ _ hx _ _
      exact ⟨false, rfl, hx⟩
    · intro _ _ _ _ h
      exact ⟨(), h⟩
    · intro _ _ _ _ h
      exact h
    · intro x _ h
      exact Bool.noConfusion (h.1.symm.trans h.2)

end TruthCore.Results.Aquinas.SummaTheologiae.CompositeUnitingCauseControls
