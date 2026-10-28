import TruthCore.Modal.Kripke

namespace TruthCore.Results.Modal.StandardCorrespondence
open TruthCore.Modal
universe u

/-- One-atom T validity under every valuation and world is exactly reflexivity.
No inhabitedness or global frame hypothesis is assumed. -/
theorem t_iff_reflexive {World : Type u} (F : Frame World) :
    Valid F (.imp (.box (.atom ())) (.atom ())) ↔ Reflexive F := by
  constructor
  · intro h w
    exact h (fun v _ => F.access w v) w (fun _ hv => hv)
  · intro h
    exact axiomT_valid F h (.atom ())

/-- One-atom D validity under every valuation and world is exactly seriality.
Empty world types satisfy both sides vacuously; no choice is required. -/
theorem d_iff_serial {World : Type u} (F : Frame World) :
    Valid F (.imp (.box (.atom ())) (.diamond (.atom ()))) ↔ Serial F := by
  constructor
  · intro h w
    obtain ⟨v, hv, _⟩ := h (fun _ _ => True) w (fun _ _ => True.intro)
    exact ⟨v, hv⟩
  · intro h
    exact axiomD_valid F h (.atom ())

end TruthCore.Results.Modal.StandardCorrespondence
