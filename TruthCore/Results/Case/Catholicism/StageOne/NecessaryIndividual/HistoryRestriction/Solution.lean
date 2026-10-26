import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.EmptyWorldFork

namespace TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.HistoryRestriction
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual

/-- Exact preservation of both populated histories under restriction, and
the consequent switch from contingent to necessary presence of the root. -/
theorem checks : HistoryOnlyCountermodel := by
  unfold HistoryOnlyCountermodel SharedRootOnPopulated
    historyOnlyExists rootedEmptyExists alternatingFrame
    TruthCore.Modal.Reflexive JointAbsence DeDicto DeRe
    TruthCore.Isabelle.AFP.GoedelGod.Box TruthCore.Isabelle.AFP.GoedelGod.Dia
  decide
end TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.HistoryRestriction
