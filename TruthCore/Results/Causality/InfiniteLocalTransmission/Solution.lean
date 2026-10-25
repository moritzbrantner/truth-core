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
  · intro hWellFounded
    have notAcc : ∀ n, ¬ Acc (fun (y x : Nat) => y = x + 1) n := by
      intro n hAcc
      induction hAcc with
      | intro x _ ih => exact ih (x + 1) rfl
    exact notAcc 0 (hWellFounded 0)

end TruthCore.Results.Causality.InfiniteLocalTransmission
