import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReceptionControl

namespace TruthCore.Results.Aquinas.SummaTheologiae.SubsistentInfinityReceptionControls
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception

/-- Each of the four reception readings is needed for the derivation of
`SubsistentBeingIsInfiniteReading`, and the four are jointly satisfiable with
a limited, non-infinite being whose esse is received in its distinct essence. -/
theorem checks : Control.Certificate := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- One being, limited esse, received nowhere, not infinite.
    refine ⟨Unit, Unit, fun _ => (), fun _ => (), fun _ => False, fun _ => True,
      fun _ _ => False, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      obtain ⟨_, hr⟩ := h () trivial
      exact hr
    · intro _ _ h
      exact h.elim
    · intro _ _ h
      exact h.elim
    · intro _ h
      exact (h trivial).elim
    · intro h
      exact h () rfl
  · -- Esse `false` received in the foreign principle `true`.
    refine ⟨Unit, Bool, fun _ => false, fun _ => false, fun _ => False, fun _ => True,
      fun _ r => r = true, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _
      exact ⟨true, rfl⟩
    · intro h
      exact Bool.noConfusion (h () true rfl)
    · intro _ r hr hEq
      exact Bool.noConfusion (hr.symm.trans hEq)
    · intro _ h
      exact (h trivial).elim
    · intro h
      exact h () rfl
  · -- One principle that receives itself.
    refine ⟨Unit, Unit, fun _ => (), fun _ => (), fun _ => False, fun _ => True,
      fun _ _ => True, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _
      exact ⟨(), trivial⟩
    · intro _ _ _
      rfl
    · intro h
      exact h () () trivial rfl
    · intro _ h
      exact (h trivial).elim
    · intro h
      exact h () rfl
  · -- Nothing limited, nothing received, nothing infinite.
    refine ⟨Unit, Unit, fun _ => (), fun _ => (), fun _ => False, fun _ => False,
      fun _ _ => False, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ h
      exact h.elim
    · intro _ _ h
      exact h.elim
    · intro _ _ h
      exact h.elim
    · intro h
      exact h () (fun h => h)
    · intro h
      exact h () rfl
  · -- Being `true` is its own esse; being `false` has esse `true` received in
    -- its distinct essence `false`, which limits it.
    refine ⟨Bool, Bool, fun x => x, fun _ => true, fun x => x = true, fun x => x = false,
      fun x r => x = false ∧ r = false, ?_, ?_, ?_, ?_, ⟨true, rfl⟩, ?_⟩
    · intro x hx
      exact ⟨false, hx, rfl⟩
    · intro x r hr
      exact hr.2.trans hr.1.symm
    · intro x r hr hEq
      exact Bool.noConfusion (hr.2.symm.trans hEq)
    · intro x hx
      cases x
      · exact (hx rfl).elim
      · rfl
    · refine ⟨false, fun h => Bool.noConfusion h, ⟨rfl, rfl⟩, rfl, fun h => Bool.noConfusion h⟩

end TruthCore.Results.Aquinas.SummaTheologiae.SubsistentInfinityReceptionControls
