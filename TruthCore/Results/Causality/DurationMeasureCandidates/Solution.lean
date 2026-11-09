module
public import TruthCore.Causality.DurationMeasureCandidates
@[expose] public section
namespace TruthCore.Results.Causality.DurationMeasureCandidates
open TruthCore.Causality.DurationMeasureCandidates

theorem timeControls : TimeControls := by
  have hl : Extensive length := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a b; rfl
    · intro a h; exact h
    · intro a h; exact h
    · intro a b c h; exact h.2.2.2.2
    · intros; rfl
    · intro a m; exact ⟨⟨m, a.start, a.extent⟩, rfl, rfl⟩
  have hb : Comparative bent := by
    intro a b
    simp only [NoLonger, bent]
    constructor <;> intro h <;> nlinarith
  refine ⟨hl, hb, ?_, ?_⟩
  · intro h
    have bad := h.2.2.2.1 ⟨false,0,1⟩ ⟨false,1,1⟩ ⟨false,0,2⟩
      (by unfold Joins; decide : Joins ⟨false,0,1⟩ ⟨false,1,1⟩ ⟨false,0,2⟩)
    norm_num [bent] at bad
  · intro h
    have bad := (h ⟨false,0,2⟩ ⟨false,0,1⟩).mpr (by decide)
    norm_num [NoLonger] at bad

theorem aevumControls : AevumControls := by
  have stable : StableWhole potential := by
    refine ⟨⟨false, rfl⟩, ?_, ?_, ?_⟩
    · intros; rfl
    · intro c _; exact ⟨(), trivial⟩
    · intro c p q _ _ _; exact Subsingleton.elim p q
  refine ⟨⟨stable, ?_, ?_⟩, ⟨stable, rfl, rfl, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · exact ⟨false, true, trivial, trivial, by decide⟩
  · intro c d hc hd; simp only [potential] at hc hd; rw [hc, hd]
  · intro h
    have bad := h.2.1 false true trivial trivial
    norm_num [corrupted, potential] at bad
end TruthCore.Results.Causality.DurationMeasureCandidates
