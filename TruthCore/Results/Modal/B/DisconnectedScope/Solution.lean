import TruthCore.Modal.BResearch
import TruthCore.Results.Modal.K.Laws.Solution
namespace TruthCore.Results.Modal.B.DisconnectedScope
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.BResearch

theorem root_full : MC separated.frame allPredicates .left := by
  apply (K.Laws.full_iff_successors _ _).mpr
  intro v hv; cases v with
  | left => rfl
  | middle => cases hv
  | right => cases hv

theorem checks : DisconnectedScope := by
  refine ⟨?_, ?_, root_full, ⟨.left, rfl, root_full⟩, ?_, ?_, ?_, ?_⟩
  · intro w; cases w <;> rfl
  · intro w v h; cases w <;> cases v <;> exact h
  · intro v hv; cases v with
    | left => exact root_full
    | middle => cases hv
    | right => cases hv
  · intro h; cases h
  · intro h; cases h
  · exact ⟨⟨.middle, rfl, rfl⟩, ⟨.right, rfl, fun h => Bool.noConfusion h⟩⟩
end TruthCore.Results.Modal.B.DisconnectedScope
