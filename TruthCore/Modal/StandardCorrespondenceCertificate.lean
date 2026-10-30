import TruthCore.Modal.Kripke

namespace TruthCore.Modal
universe u

/-- Transparent delivery bundle of the two named T/D frame correspondences.
Validity ranges over every valuation and world; no world inhabitedness, frame
condition, causal interpretation or Hilbert completeness is assumed. -/
def StandardCorrespondenceCertificate : Prop :=
  (∀ (World : Type u) (F : Frame World),
    Valid F (.imp (.box (.atom ())) (.atom ())) ↔ Reflexive F) ∧
  (∀ (World : Type u) (F : Frame World),
    Valid F (.imp (.box (.atom ())) (.diamond (.atom ()))) ↔ Serial F)

end TruthCore.Modal
