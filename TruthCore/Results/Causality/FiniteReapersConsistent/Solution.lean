import TruthCore.Causality.GrimReaper

namespace TruthCore.Results.Causality.FiniteReapersConsistent
open TruthCore.Causality

/-- The first-deadline Reaper (index 2) acts; the others do not. -/
theorem finiteReapersConsistent : ConsistentFiniteThreeReapers := by
  -- Explicit constructors keep the finite model independent of numeral
  -- instances and propositional simplification lemmas that use propext.
  refine ⟨fun n => n = ⟨2, Nat.lt_succ_self 2⟩, ?_⟩
  intro ⟨n, bound⟩
  cases n with
  | zero =>
    constructor
    · intro h
      exact Nat.noConfusion (congrArg Fin.val h)
    · intro h
      exact False.elim (h ⟨2, Nat.lt_succ_self 2⟩ (Nat.zero_lt_succ 1) rfl)
  | succ n =>
    cases n with
    | zero =>
      constructor
      · intro h
        exact Nat.noConfusion (Nat.succ.inj (congrArg Fin.val h))
      · intro h
        exact False.elim (h ⟨2, Nat.lt_succ_self 2⟩ (Nat.lt_succ_self 1) rfl)
    | succ n =>
      cases n with
      | zero =>
        constructor
        · intro _ m hlt
          exact False.elim (Nat.not_le_of_gt m.isLt (Nat.succ_le_of_lt hlt))
        · intro _
          rfl
      | succ n =>
        exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 3 n) bound)

end TruthCore.Results.Causality.FiniteReapersConsistent
