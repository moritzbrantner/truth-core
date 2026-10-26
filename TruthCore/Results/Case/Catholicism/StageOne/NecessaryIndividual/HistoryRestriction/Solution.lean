import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.EmptyWorldFork

namespace TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.HistoryRestriction
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual

/-- The same root is present in either selected populated history. -/
private theorem rootPresent (history : Bool) : historyOnlyExists 0 history := by
  cases history <;> decide

/-- Exact preservation of both populated histories under restriction, and
the consequent switch from contingent to necessary presence of the root. -/
theorem checks : HistoryOnlyCountermodel := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro world
    trivial
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
end TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.HistoryRestriction
