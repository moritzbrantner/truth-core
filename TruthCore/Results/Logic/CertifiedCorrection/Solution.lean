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
        exact ⟨rfl, rfl⟩
      · intro s _ b c h
        cases b
        · exact Bool.noConfusion h
        · exact ⟨fun _ => trivial, fun _ => rfl⟩
    · constructor
      · constructor
        · intro s _
          exact ⟨rfl, rfl⟩
        · intro h
          have bad := h false trivial true 0 (by decide)
          exact Bool.noConfusion (bad.mp rfl)
      · constructor
        · constructor
          · exact ⟨fun s => s = true, fun _ => Iff.rfl⟩
          · intro h
            have bad := (h true trivial).1
            exact Bool.noConfusion bad
        · constructor
          · intro s hs b c h
            cases b
            · exact Bool.noConfusion h
            · exact ⟨fun _ => hs, fun _ => rfl⟩
          · intro h
            have bad := h false trivial true 0 (by decide)
            exact Bool.noConfusion (bad.mp rfl)
end TruthCore.Results.Logic.CertifiedCorrection
