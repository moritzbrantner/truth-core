import TruthCore.Modal.AccessibilityComponents

namespace TruthCore.Results.Modal.AccessibilityComponents
open TruthCore.Modal
universe u

/-- SCCs are exactly accessibility equivalence classes; weak connectivity alone
cannot identify them. Nil paths are included, hence reflexivity is explicit. -/
theorem certificate : TruthCore.Modal.AccessibilityComponents.Certificate.{u} := by
  constructor
  · intro World F hr hs ht a b
    let := F.toQuiver
    rw [Quiver.StronglyConnectedComponent.eq]
    change (Quiver.Reachable a b ∧ Quiver.Reachable b a) ↔ F.access a b
    rw [GraphBridge.reachable_iff_access F hr ht a b,
      GraphBridge.reachable_iff_access F hr ht b a]
    exact ⟨And.left, fun h => ⟨h, hs a b h⟩⟩
  · let F := TruthCore.Modal.AccessibilityComponents.oneWay
    let := F.toQuiver
    have hr : Reflexive F := fun a => le_refl a
    have ht : Transitive F := fun _ _ _ => le_trans
    constructor
    · intro a b
      apply (Quiver.WeaklyConnectedComponent.eq a b).2
      cases a <;> cases b
      · exact ⟨Quiver.Path.nil⟩
      · exact ⟨(Quiver.Hom.toPath (Sum.inl (PLift.up (show F.access false true from by change false ≤ true; decide)) ))⟩
      · exact ⟨(Quiver.Hom.toPath (Sum.inr (PLift.up (show F.access false true from by change false ≤ true; decide)) ))⟩
      · exact ⟨Quiver.Path.nil⟩
    · intro h
      have paths := (Quiver.StronglyConnectedComponent.eq false true).1 h
      have back := (GraphBridge.reachable_iff_access F hr ht true false).1 paths.2
      exact (by decide : ¬ (true ≤ false)) back

end TruthCore.Results.Modal.AccessibilityComponents
