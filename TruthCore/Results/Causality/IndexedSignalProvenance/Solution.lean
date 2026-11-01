import TruthCore.Causality.IndexedSignalProvenance

namespace TruthCore.Results.Causality.IndexedSignalProvenance
open TruthCore.Causality.IndexedSignalProvenance

/-- Finite code bounds and unchanged local forwarding suffice for issuance
at the named station, without global chain well-foundedness. -/
theorem provenance (signal : Nat → Option Nat) (issued : Nat → Prop)
    (hConserve : LocalConservation signal issued)
    (hBound : IndexAdmissible signal) : GlobalProvenance signal issued := by
  intro n j hs
  have walk : ∀ steps, issued j ∨ signal (n + steps) = some j := by
    intro steps
    induction steps with
    | zero => exact Or.inr hs
    | succ steps ih =>
      rcases ih with hi | hf
      · exact Or.inl hi
      · rcases hConserve (n + steps) j hf with ⟨hi, hj⟩ | hnext
        · exact Or.inl (hj ▸ hi)
        · exact Or.inr hnext
  rcases walk (j + 1) with hi | hf
  · exact hi
  · have h := hBound (n + (j + 1)) j hf
    exact (Nat.not_succ_le_self j (Nat.le_trans (Nat.le_add_left (j + 1) n) h)).elim

/-- Delete either local interface, and retain the other on the same Nat
carrier. A quiet model also prevents reading a firing law into the premises. -/
theorem controls : Controls := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun _ => some 0, fun _ => False, ?_, ?_, ?_⟩
    · intro _ _ h
      exact Or.inr h
    · intro h
      have hn := h 1 0 rfl
      exact Nat.not_succ_le_zero 0 hn
    · intro h
      exact h 0 0 rfl
  · refine ⟨fun n => if n = 0 then some 0 else none, fun _ => False, ?_, ?_, ?_⟩
    · intro n j hs
      dsimp only at hs
      split at hs
      · cases hs
        rename_i hn
        exact Nat.le_of_eq hn
      · cases hs
    · intro h
      rcases h 0 0 rfl with ⟨hi, _⟩ | hf
      · exact hi
      · cases hf
    · intro h
      exact h 0 0 rfl
  · refine ⟨fun _ => none, fun _ => False, ?_, ?_, ?_, ?_⟩
    · intro _ _ h
      cases h
    · intro _ _ h
      cases h
    · intro _
      rfl
    · intro _ h
      exact h

end TruthCore.Results.Causality.IndexedSignalProvenance
