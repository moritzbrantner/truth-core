import TruthCore.Modal.Kripke

namespace TruthCore.Results.Modal.StandardCorrespondence
open TruthCore.Modal
universe u

/-- One-atom T validity under every valuation and world is exactly reflexivity.
No inhabitedness or global frame hypothesis is assumed. -/
theorem t_iff_reflexive {World : Type u} (F : Frame World) :
    Valid F (.imp (.box (.atom ())) (.atom ())) ↔ Reflexive F := by
  sorry

/-- One-atom D validity under every valuation and world is exactly seriality.
Empty world types satisfy both sides vacuously; no choice is required. -/
theorem d_iff_serial {World : Type u} (F : Frame World) :
    Valid F (.imp (.box (.atom ())) (.diamond (.atom ()))) ↔ Serial F := by
  sorry

end TruthCore.Results.Modal.StandardCorrespondence
