import TruthCore.Results.Modal.B.Laws.Solution
namespace TruthCore.Results.Modal.B.NecessarySymmetry
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.BResearch

theorem checks : NecessarySymmetry := by
  intro W F w hs
  constructor
  · intro h v hv
    have he := (K.Laws.full_iff_successors F w).mp h v hv
    rw [he]
    exact h
  · intro h
    apply (K.Laws.full_iff_successors F w).mpr
    intro v hv
    exact (Laws.back_edge F allPredicates w v (hs w v hv) trivial (h v hv)).symm
end TruthCore.Results.Modal.B.NecessarySymmetry
