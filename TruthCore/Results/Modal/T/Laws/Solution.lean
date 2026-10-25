import TruthCore.Modal.TResearch
import TruthCore.Results.Modal.K.Laws.Solution
namespace TruthCore.Results.Modal.T.Laws
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.TResearch
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)

theorem checks : Laws := by
  constructor
  · intro W F hRef w
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · intro h v
        constructor
        · exact (K.Laws.full_iff_successors F w).mp h v
        · intro he; rw [he]; exact hRef w
      · intro h
        exact (K.Laws.full_iff_successors F w).mpr (fun v hv => (h v).mp hv)
    · constructor
      · intro h v hv
        rw [(K.Laws.full_iff_successors F w).mp h v hv]
        exact h
      · intro h; exact h w (hRef w)
    · intro h; exact ⟨w, hRef w, h⟩
  · intro W F D hRef w
    exact ⟨fun h => h w (hRef w), fun h => ⟨w, hRef w, h⟩⟩
end TruthCore.Results.Modal.T.Laws
