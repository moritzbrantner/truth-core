import TruthCore.Causality.LocalTransmission

namespace TruthCore.Results.Causality.InfiniteLocalTransmission
open TruthCore.Causality

/-- Pure order plus a local dependence law does not imply a first source.
The model's uniformly active chain is consistent; interpreting the relation
as genuinely derivative efficient causation remains disputed. -/
theorem infiniteLocalTransmission : InfiniteLocalTransmissionModel := by
  refine ⟨(fun y x => y = x + 1), (fun _ => True), ?_, ?_, trivial, ?_⟩
  · intro n
    rfl
  · intro n
    rfl
  · exact successorChainNotWellFounded

end TruthCore.Results.Causality.InfiniteLocalTransmission
