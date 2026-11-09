module
public import TruthCore.Logic.CertifiedCorrection

@[expose] public section
namespace TruthCore.Results.Logic.CertifiedCorrection
open TruthCore.Logic.CertifiedCorrection

theorem connectionAndControls : ConnectionAndControls := by
  constructor
  · intro State Evidence p observe scope Correct covered calibrated
    refine ⟨fun e => p.decide e = true, ?_⟩
    intro s
    exact calibrated s.val s.property _ _ (covered s.val s.property).2
  · constructor
    · constructor
      · intro s _
        simp [echo]
      · intro s _ b c h
        simp [echo] at h
        simp [h]
    · constructor
      · constructor
        · intro s _
          simp [echo]
        · intro h
          have bad := h false trivial true 0 (by decide)
          simp at bad
      · constructor
        · constructor
          · exact ⟨fun s => s = true, fun _ => Iff.rfl⟩
          · intro h
            have bad := (h true trivial).1
            simp [echo] at bad
        · constructor
          · intro s hs b c h
            simp [echo] at h
            simp [h, hs]
          · intro h
            have bad := h false trivial true 0 (by decide)
            simp at bad
end TruthCore.Results.Logic.CertifiedCorrection
