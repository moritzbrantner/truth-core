import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.EmptyWorldFork

namespace TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.HistoryRestriction
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual

/-- The same root is present in either selected populated history. -/
private theorem rootPresent (history : Bool) : historyOnlyExists 0 history := by
  cases history with
  | false =>
    change (1 : Fin 3) ≠ 0 ∧ ((0 : Fin 3) = 0 ∨ 0 = 1)
    exact ⟨firstHistory_ne_empty, Or.inl rfl⟩
  | true =>
    change (2 : Fin 3) ≠ 0 ∧ ((0 : Fin 3) = 0 ∨ 0 = 2)
    exact ⟨secondHistory_ne_empty, Or.inl rfl⟩

/-- Exact preservation of both populated histories under restriction, and
the consequent switch from contingent to necessary presence of the root. -/
theorem checks : HistoryOnlyCountermodel := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro world
    exact True.intro
  · intro x
    rfl
  · intro x
    rfl
  · intro next _ _
    exact rootPresent next
  · intro next _
    exact ⟨0, rootPresent next⟩
  · exact ⟨0, fun next _ => rootPresent next⟩
  · rintro ⟨next, _, hEmpty⟩
    exact hEmpty ⟨0, rootPresent next⟩
#print axioms rootPresent
#print axioms checks
end TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.HistoryRestriction
