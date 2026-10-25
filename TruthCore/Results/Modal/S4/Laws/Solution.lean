import TruthCore.Modal.S4Research
import TruthCore.Results.Modal.K.Laws.Solution
namespace TruthCore.Results.Modal.S4.Laws
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.S4Research
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)

theorem necessary {W : Type} (F : Frame W) w
    (h : MC F allPredicates w) : Box F (MC F allPredicates) w := by
  intro v hv
  have he := (K.Laws.full_iff_successors F w).mp h v hv
  rw [he]
  exact h

theorem symmetric_transfer {W : Type} (F : Frame W) w
    (hs : Symmetric F) (h : Dia F (MC F allPredicates) w) :
    MC F allPredicates w := by
  obtain ⟨v, hv, hm⟩ := h
  have he := (K.Laws.full_iff_successors F v).mp hm w (hs w v hv)
  rw [he]
  exact hm

theorem checks : TruthCore.Modal.S4Research.Laws := by
  refine ⟨?_, ?_, ?_⟩
  · intro W F w hr
    exact ⟨necessary F w, fun h => h w (hr w)⟩
  · intro W F w v hm hc
    exact (K.Laws.full_iff_successors F w).mp hm v hc.1
  · intro W F w hs hm
    exact symmetric_transfer F w hs hm
end TruthCore.Results.Modal.S4.Laws
