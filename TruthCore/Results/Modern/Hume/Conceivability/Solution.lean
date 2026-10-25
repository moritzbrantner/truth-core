import TruthCore.Modern.Hume.Conceivability
namespace TruthCore.Results.Modern.Hume.Conceivability
open TruthCore.Modal
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Modern.Hume.Conceivability

private theorem separation (W : Type) (F : Frame W) w (h : Collapse F w) :
    ∀ v, F.access w v → v = w := by
  intro v hv
  exact h (fun x => x = w) rfl v hv

private theorem component (W : Type) (F : Frame W)
    (hs : Symmetric F) (ht : Transitive F) w
    (h : Dia F (Collapse F) w) : Collapse F w := by
  obtain ⟨v, hwv, hc⟩ := h
  have hvw := hs w v hwv
  intro P hp z hwz
  have hzw := separation W F v hc z (ht v w z hvw hwz)
  have hwv' := separation W F v hc w hvw
  exact hzw.symm ▸ (hwv' ▸ hp)

private theorem obstruction (W : Type) (F : Frame W)
    (hs : Symmetric F) (ht : Transitive F) w (P : MProp W)
    (hc : Contingent F P w) (hm : Dia F (Collapse F) w) : False := by
  have hcol := component W F hs ht w hm
  obtain ⟨⟨a, ha, hpa⟩, ⟨b, hb, hnpb⟩⟩ := hc
  have haw := separation W F w hcol a ha
  have hbw := separation W F w hcol b hb
  exact hnpb (hbw.symm ▸ (haw ▸ hpa))

 theorem checks : Checks := by
  refine ⟨?_, ?_, separation, component, obstruction, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W F C w hH hC
    exact hH _ hC
  · intro W F C w hH hC hN
    obtain ⟨v, hv, hn⟩ := hH _ hC
    exact hn (hN v hv)
  · intro W F C hs ht w P hc hH hC
    exact obstruction W F hs ht w P hc (hH _ hC)
  · intro h
    obtain ⟨_, _, hf⟩ := h (fun _ => False) True.intro
    exact hf
  · have hFalse : StrongBridge universal selfC false := by
      intro P h
      rcases h with ⟨_, hp⟩ | hf
      · exact ⟨true, True.intro, hp⟩
      · cases hf
    have hTrue : ¬ StrongBridge universal selfC true := by
      intro h
      obtain ⟨_, _, hf⟩ := h (fun _ => False) (Or.inr rfl)
      exact hf
    exact ⟨hFalse, Or.inl ⟨rfl, hTrue⟩⟩
  · exact ⟨⟨true, True.intro, rfl⟩, ⟨false, True.intro, Bool.false_ne_true⟩⟩
  · have hc : Collapse branching true := by
      intro P hp v hv
      rcases hv with hf | hv
      · cases hf
      · exact hv.symm ▸ hp
    refine ⟨?_, ?_, ⟨true, Or.inl rfl, hc⟩, ?_⟩
    · intro w
      cases w with
      | false => exact Or.inl rfl
      | true => exact Or.inr rfl
    · intro w m v hwm hmv
      rcases hwm with hw | hm
      · exact Or.inl hw
      · rcases hmv with hm' | hv
        · cases hm.symm.trans hm'
        · exact Or.inr hv
    · intro h
      have bad := h (fun w => w = false) rfl true (Or.inl rfl)
      cases bad
  · exact ⟨fun h => h, fun _ h => False.elim h⟩
  · exact ⟨fun P hp v hv => hv.symm ▸ hp, Bool.false_ne_true⟩
end TruthCore.Results.Modern.Hume.Conceivability
