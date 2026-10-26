import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.EmptyWorldFork

namespace TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.RootedEmpty
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual

/-- Exhaustive finite check of the three-world/three-individual interpretation,
including its separate one-step causal bound. -/
theorem checks : RootedEmptyCountermodel := by
  unfold RootedEmptyCountermodel RootedEmptyDependentCoverage
    RootedEmptyNoTwoStepCause SharedRootOnPopulated
    rootedEmptyFrame rootedEmptyExists rootedEmptyCauses
    TruthCore.Modal.Reflexive JointAbsence DeDicto DeRe
    TruthCore.Isabelle.AFP.GoedelGod.Box TruthCore.Isabelle.AFP.GoedelGod.Dia
  decide
end TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.RootedEmpty
