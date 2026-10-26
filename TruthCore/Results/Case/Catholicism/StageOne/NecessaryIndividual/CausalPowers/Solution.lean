import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.CausalPowers
namespace TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.CausalPowers
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
open TruthCore.Isabelle.AFP.GoedelGod (Box)
/-- Satisfiability of the specified response theory, not metaphysical possibility. -/
theorem checks : CausalPowers.Compatibility := by
  have h : Box alternatingFrame
      (ConcreteAt CausalPowers.existsAt
        (CausalPowers.Capacity alternatingFrame CausalPowers.existsAt CausalPowers.response)
        false) false := by
    unfold Box ConcreteAt CausalPowers.Capacity alternatingFrame CausalPowers.existsAt
      CausalPowers.response
    decide
  have hd := deRe_to_deDicto alternatingFrame
    (ConcreteAt CausalPowers.existsAt
      (CausalPowers.Capacity alternatingFrame CausalPowers.existsAt CausalPowers.response))
    false ⟨false, h⟩
  unfold CausalPowers.Compatibility
  refine ⟨?_, trivial, Bool.noConfusion, ?_, ?_, ?_, ?_, hd, ?_⟩
  all_goals
    try unfold TruthCore.Modal.Reflexive
    try unfold Box
    try unfold CausalPowers.Capacity
    try unfold CausalPowers.Disciplined
    try unfold alternatingFrame
    try unfold CausalPowers.existsAt
    try unfold CausalPowers.response
    decide
end TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.CausalPowers
