import TruthCore.Modal.KResearch
namespace TruthCore.Results.Modal.K.Laws
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.KResearch
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Modern.Hume.Conceivability (Contingent)

theorem full_iff_successors {W : Type} (F : Frame W) (w : W) :
    MC F allPredicates w ↔ ∀ v, F.access w v → v = w := by
  constructor
  · exact identity_separates F allPredicates w trivial
  · intro h P _ hp v hv
    rw [h v hv]
    exact hp

theorem full_iff_actuality {W : Type} (F : Frame W) (w : W) :
    MC F allPredicates w ↔ PossibilityActuality F allPredicates w := by
  constructor
  · intro h P _ ⟨v, hv, hp⟩
    have he := (full_iff_successors F w).mp h v hv
    rw [he] at hp
    exact hp
  · intro h
    apply (full_iff_successors F w).mpr
    intro v hv
    have he : w = v := h (fun x => x = v) trivial ⟨v, hv, rfl⟩
    exact he.symm

theorem dead_end {W : Type} (F : Frame W) (D : Domain W) (w : W)
    (h : ∀ v, ¬ F.access w v) :
    MC F D w ∧ Box F (MC F D) w ∧ ¬ Dia F (MC F D) w := by
  refine ⟨?_, ?_, ?_⟩
  · intro P _ _ v hv; exact (h v hv).elim
  · intro v hv; exact (h v hv).elim
  · rintro ⟨v, hv, _⟩; exact h v hv

theorem no_contingency {W : Type} (F : Frame W) (w : W) (P : MProp W)
    (h : MC F allPredicates w) : ¬ Contingent F P w := by
  intro hc
  have ha := (full_iff_actuality F w).mp h
  exact ha (fun v => ¬ P v) trivial hc.2 (ha P trivial hc.1)

theorem checks : Laws := by
  exact ⟨fun _ F w => full_iff_successors F w,
    fun _ F w => full_iff_actuality F w,
    fun _ F D w => dead_end F D w,
    fun _ F w P => no_contingency F w P⟩
end TruthCore.Results.Modal.K.Laws
