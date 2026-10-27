import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.EmptyWorldFork

namespace TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.HistoryRestriction
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual

/-- The same root is present in either selected populated history. -/
private theorem rootPresent (history : Bool) : historyOnlyExists rootedZero history := by
  cases history with
  | false =>
    change rootedOne ≠ rootedZero ∧ (rootedZero = rootedZero ∨ rootedZero = rootedOne)
    exact ⟨firstHistory_ne_empty, Or.inl rfl⟩
  | true =>
    change rootedTwo ≠ rootedZero ∧ (rootedZero = rootedZero ∨ rootedZero = rootedTwo)
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
    exact ⟨rootedZero, rootPresent next⟩
  · exact ⟨rootedZero, fun next _ => rootPresent next⟩
  · rintro ⟨next, _, hEmpty⟩
    exact hEmpty ⟨rootedZero, rootPresent next⟩
end TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.HistoryRestriction
