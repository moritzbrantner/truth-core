import TruthCore.Logic.KnowledgeRetorsion

namespace TruthCore.Results.Logic.KnowledgeRetorsion
open TruthCore.Logic.KnowledgeRetorsion

universe u

/-- Knowing the universal denial would, by factivity, make it true, and hence
refute the alleged knowledge of that very proposition. -/
theorem noFactiveKnowerOfUniversalNoKnowledge :
    NoFactiveKnowerOfUniversalNoKnowledge.{u} := by
  intro Agent Knows hFactive a hKnows
  have hDenial : UniversalNoKnowledge Knows := hFactive a _ hKnows
  exact hDenial a _ hKnows

/-- A nonempty agent can assert the denial without knowing anything. -/
theorem assertedNoKnowledgeModel : AssertedNoKnowledgeModel := by
  refine ⟨(fun _ _ => False), (fun _ _ => True), ?_, ?_, ?_⟩
  · intro _ _ h
    exact h.elim
  · intro _ _ h
    exact h.elim
  · trivial

/-- Without factivity, a predicate named Knows can hold of the false denial. -/
theorem nonfactiveKnownNoKnowledgeModel : NonfactiveKnownNoKnowledgeModel := by
  let Knows : Unit → Prop → Prop := fun _ p => ¬ p
  have hNotAll : ¬ UniversalNoKnowledge Knows := by
    intro hAll
    exact hAll () False (fun hFalse => hFalse.elim)
  refine ⟨Knows, ?_, ?_⟩
  · exact hNotAll
  · intro hFactive
    exact hFactive () False (fun hFalse => hFalse.elim)

end TruthCore.Results.Logic.KnowledgeRetorsion
