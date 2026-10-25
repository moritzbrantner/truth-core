import TruthCore.Modal.BResearch
import TruthCore.Results.Modal.K.Laws.Solution
namespace TruthCore.Results.Modal.B.Laws
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.BResearch
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)

theorem back_edge {W : Type} (F : Frame W) (D : Domain W) (w v : W)
    (hBack : F.access v w) (hId : IdentityAdmissible D v) (h : MC F D v) :
    w = v := identity_separates F D v hId h w hBack

theorem possible_full {W : Type} (F : Frame W) (w : W)
    (hSym : Symmetric F) (h : Dia F (MC F allPredicates) w) :
    MC F allPredicates w := by
  obtain ⟨v, hv, hc⟩ := h
  have he := back_edge F allPredicates w v (hSym w v hv) trivial hc
  rw [he]
  exact hc

theorem checks : Laws := by
  refine ⟨fun _ F D w v => back_edge F D w v,
    fun _ F w => possible_full F w, ?_⟩
  intro W F w hr hs
  constructor
  · constructor
    · intro h; exact ⟨w, hr w, h⟩
    · exact possible_full F w hs
  · constructor
    · intro h v hv
      have he := (K.Laws.full_iff_successors F w).mp h v hv
      rw [he]
      exact h
    · intro h; exact h w (hr w)
end TruthCore.Results.Modal.B.Laws
