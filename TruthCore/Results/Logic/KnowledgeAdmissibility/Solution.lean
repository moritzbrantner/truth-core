module

public import TruthCore.Logic.KnowledgeAdmissibility

@[expose] public section
namespace TruthCore.Results.Logic.KnowledgeAdmissibility
open TruthCore.Logic.KnowledgeAdmissibility
open TruthCore.Modal
open TruthCore.Modal.PossibilityTransfer (IncludedAt)
open TruthCore.Logic.JustificationIntrospection (Knows)

theorem admissibility : AdmissibilityLaw := by
  intro W P Q E M p q a hSuper hPhysical hIncluded
  have transferred := (TruthCore.Results.Modal.PossibilityTransfer.box_transfer_iff
    W E M a).mpr hIncluded _ hSuper
  intro v hv
  exact transferred v hv (hPhysical v hv)

private theorem episode : SharedEpisode := by
  have ignorance : ¬ Knows epistemic (fun v => phenomenal v = phenomenal actual) actual := by
    intro h
    exact Bool.noConfusion (h (false, true) rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ignorance, ?_⟩
  · intro w; rfl
  · intro w v h; exact h.symm
  · intro w v u h1 h2; exact h2.trans h1
  · intro w; exact ⟨rfl, rfl⟩
  · intro w v h; exact ⟨h.1.symm, h.2.symm⟩
  · intro w v u h1 h2; exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
  · intro f hf v hv
    change f (physical v)
    exact hv.symm ▸ hf
  · intro f hf v hv
    change f (physical v)
    exact hv.1.symm ▸ hf
  · intro v hv; exact hv
  · intro v hv; exact hv.2

private theorem survivor : SupervenientSurvivor := by
  have hs : SupervenesAt supervenient physical phenomenal actual := by
    intro v hv hp
    have diagonal : physical v = phenomenal v := hv.mpr rfl
    exact diagonal.symm.trans hp
  refine ⟨?_, ?_, ?_, hs, ?_, ?_, ?_⟩
  · intro w; exact Iff.rfl
  · intro w v h; exact h.symm
  · intro w v u h1 h2; exact h2.trans h1
  · exact ⟨(true, true), ⟨fun _ => rfl, fun _ => rfl⟩, Bool.noConfusion⟩
  · rintro ⟨v, hv, hp, hq⟩
    exact hq (hs v hv hp)
  · intro inclusion
    exact episode.2.2.2.2.2.2.2.2.2.1
      (admissibility Description Bool Bool epistemic supervenient physical phenomenal actual
        hs episode.2.2.2.2.2.2.2.2.1 inclusion)

private theorem rival : TwinRival := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; trivial
  · intro _ _ _; trivial
  · intro _ _ _ _ _; trivial
  · intro _ _; trivial
  · exact ⟨(false, true), trivial, rfl, Bool.noConfusion⟩
  · intro h
    exact Bool.noConfusion (h (false, true) trivial rfl)

theorem checks : Certificate := ⟨admissibility, episode, survivor, rival⟩

end TruthCore.Results.Logic.KnowledgeAdmissibility
