import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.Quantifiers

namespace TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.Alternating
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual

/-- Mathematical quantifier diagnostic only; no metaphysical possibility claim. -/
theorem checks : AlternatingCountermodel := by
  unfold AlternatingCountermodel TruthCore.Modal.Reflexive IndividualContingency DeDicto DeRe JointAbsence
    alternatingFrame alternatingExists alternatingConcrete ConcreteAt
    TruthCore.Isabelle.AFP.GoedelGod.Box TruthCore.Isabelle.AFP.GoedelGod.Dia
    TruthCore.Latin.Aquinas.SummaTheologiae.AllCanNotBeThenNothingPossibleReading
    TruthCore.Latin.Aquinas.SummaTheologiae.PossibleNotToBe
  decide
end TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.Alternating
