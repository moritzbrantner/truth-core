import TruthCore.Logic.JustificationIntrospection

namespace TruthCore.Results.Logic.JustificationIntrospection
open TruthCore.Modal TruthCore.Logic.JustificationIntrospection

/-- Reuse modal axiom 4; apply the independently supplied norm at each alternative. -/
theorem introspectionTransfer : IntrospectionTransfer := by
  intro W F p justified trans norm w
  have transfer : Knows F p w → Knows F justified w := by
    intro hp v hv
    have hkk := axiom4_valid F trans (Formula.atom ()) (fun v (_ : Unit) => p v) w hp
    exact norm v (hkk v hv)
  exact ⟨transfer, fun hj hp => hj (transfer hp)⟩

private def w0 : Fin 3 := ⟨0, by decide⟩
private def w1 : Fin 3 := ⟨1, by decide⟩
private def w2 : Fin 3 := ⟨2, by decide⟩

private def exampleFrame : Frame (Fin 3) where
  access a b := a = b ∨ (a = w0 ∧ b = w1) ∨ (a = w1 ∧ b = w2)

private def exampleTruth (w : Fin 3) : Prop := w ≠ w2
private def exampleJustification (w : Fin 3) : Prop := w = w0

private theorem zero_ne_one : (w0 : Fin 3) ≠ w1 := by
  intro h
  have bad : (0 : Nat) = 1 := congrArg Fin.val h
  exact Nat.noConfusion bad

private theorem zero_ne_two : (w0 : Fin 3) ≠ w2 := by
  intro h
  have bad : (0 : Nat) = 2 := congrArg Fin.val h
  exact Nat.noConfusion bad

private theorem one_ne_two : (w1 : Fin 3) ≠ w2 := by
  intro h
  have bad : (1 : Nat) = 2 := congrArg Fin.val h
  exact Nat.noConfusion (Nat.succ.inj bad)

/-- A reflexive three-world frame: w0 sees w1, w1 sees w2, but w0 does not see w2.
The proposition is true at w0 and w1; only w0 knows it and is justified. -/
theorem higherOrderIgnoranceBoundary : HigherOrderIgnoranceBoundary := by
  refine ⟨exampleFrame, exampleTruth, exampleJustification, w0, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · intro w
    exact Or.inl rfl
  · intro trans
    have bad := trans w0 w1 w2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) (Or.inr (Or.inr ⟨rfl, rfl⟩))
    rcases bad with h | ⟨_, h⟩ | ⟨h, _⟩
    · exact zero_ne_two h
    · exact one_ne_two h.symm
    · exact zero_ne_one h
  · intro w hp
    have hw : w = w0 ∨ w = w1 ∨ w = w2 := by
      rcases w with ⟨n, hn⟩
      cases n with
      | zero => exact Or.inl rfl
      | succ n =>
        cases n with
        | zero => exact Or.inr (Or.inl rfl)
        | succ n =>
          cases n with
          | zero => exact Or.inr (Or.inr rfl)
          | succ n =>
            exact False.elim (Nat.not_lt_zero n
              (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
                (Nat.lt_of_succ_lt_succ hn))))
    rcases hw with h | h | h
    · exact h
    · cases h
      exact False.elim (hp w2 (Or.inr (Or.inr ⟨rfl, rfl⟩)) rfl)
    · cases h
      exact False.elim (hp w2 (Or.inl rfl) rfl)
  · intro v hv
    rcases hv with h | ⟨_, h⟩ | ⟨h, _⟩
    · cases h
      exact zero_ne_two
    · cases h
      exact one_ne_two
    · exact False.elim (zero_ne_one h)
  · intro hj
    have bad := hj w1 (Or.inr (Or.inl ⟨rfl, rfl⟩))
    exact zero_ne_one bad.symm

/-- The checked transfer does not turn higher-order ignorance into ignorance
without its explicit transitivity and global norm conditions. -/
theorem introspectionBoundary : IntrospectionBoundary :=
  ⟨introspectionTransfer, higherOrderIgnoranceBoundary⟩

end TruthCore.Results.Logic.JustificationIntrospection
