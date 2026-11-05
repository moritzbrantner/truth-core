module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReceptionControl

@[expose] public section

namespace TruthCore.Results.Aquinas.SummaTheologiae.SubsistentInfinityReceptionControls
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception

/-- Each of the five reception premises is needed for the derivation of
`SubsistentBeingIsInfiniteReading`, and the five are jointly satisfiable with
a limited, non-infinite being whose esse is received in its distinct essence. -/
theorem checks : Control.Certificate := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- One being, limited esse, received nowhere, not infinite.
    refine ⟨Unit, Unit, fun _ => (), fun _ => (), fun _ => False, fun _ => True,
      fun _ _ => False, fun _ _ => False, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      obtain ⟨_, hr⟩ := h () trivial
      exact hr
    · intro _ _ h
      exact h.elim
    · intro _ _ h
      exact h.elim
    · intro _ h
      exact h
    · intro _ h
      exact (h trivial).elim
    · intro h
      exact h () rfl
  · -- Esse `false` received in the foreign principle `true`, which is in
    -- potency to it.
    refine ⟨Unit, Bool, fun _ => false, fun _ => false, fun _ => False, fun _ => True,
      fun _ r => r = true, fun p a => p = true ∧ a = false, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _
      exact ⟨true, rfl⟩
    · intro h
      exact Bool.noConfusion (h () true rfl)
    · intro _ r hr
      exact ⟨hr, rfl⟩
    · intro p h
      exact Bool.noConfusion (h.1.symm.trans h.2)
    · intro _ h
      exact (h trivial).elim
    · intro h
      exact h () rfl
  · -- One principle receives itself but is in potency to nothing.
    refine ⟨Unit, Unit, fun _ => (), fun _ => (), fun _ => False, fun _ => True,
      fun _ _ => True, fun _ _ => False, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _
      exact ⟨(), trivial⟩
    · intro _ _ _
      rfl
    · intro h
      exact h () () trivial
    · intro _ h
      exact h
    · intro _ h
      exact (h trivial).elim
    · intro h
      exact h () rfl
  · -- One principle receives itself and is in potency to itself.
    refine ⟨Unit, Unit, fun _ => (), fun _ => (), fun _ => False, fun _ => True,
      fun _ _ => True, fun _ _ => True, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _
      exact ⟨(), trivial⟩
    · intro _ _ _
      rfl
    · intro _ _ _
      trivial
    · intro h
      exact h () trivial
    · intro _ h
      exact (h trivial).elim
    · intro h
      exact h () rfl
  · -- Nothing limited, received, in potency or infinite.
    refine ⟨Unit, Unit, fun _ => (), fun _ => (), fun _ => False, fun _ => False,
      fun _ _ => False, fun _ _ => False, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ h
      exact h.elim
    · intro _ _ h
      exact h.elim
    · intro _ _ h
      exact h.elim
    · intro _ h
      exact h
    · intro h
      exact h () (fun h => h)
    · intro h
      exact h () rfl
  · -- Being `true` is its own esse. Being `false` has esse `true` received in its
    -- distinct essence `false`, which is in potency to it and limits it.
    refine ⟨Bool, Bool, fun x => x, fun _ => true, fun x => x = true, fun x => x = false,
      fun x r => x = false ∧ r = false, fun p a => p = false ∧ a = true,
      ?_, ?_, ?_, ?_, ?_, ⟨true, rfl⟩, ?_⟩
    · intro x hx
      exact ⟨false, hx, rfl⟩
    · intro x r hr
      exact hr.2.trans hr.1.symm
    · intro x r hr
      exact ⟨hr.2, rfl⟩
    · intro p h
      exact Bool.noConfusion (h.1.symm.trans h.2)
    · intro x hx
      cases x
      · exact (hx rfl).elim
      · rfl
    · exact ⟨false, fun h => Bool.noConfusion h, ⟨rfl, rfl⟩, rfl, fun h => Bool.noConfusion h⟩

end TruthCore.Results.Aquinas.SummaTheologiae.SubsistentInfinityReceptionControls
