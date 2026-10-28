import TruthCore.Results.Modal.GraphBridge.Solution
import Mathlib.Combinatorics.Quiver.ConnectedComponent

/-! Accessibility components use Mathlib's possibly empty paths. These are
modal graph facts, with no causal or temporal interpretation. -/
namespace TruthCore.Modal.AccessibilityComponents
universe u

/-- A reflexive one-way two-world frame, stipulated as a mathematical control. -/
def oneWay : Frame Bool := ⟨fun a b => a ≤ b⟩

/-- Universal SCC/access equivalence under all three equivalence conditions,
and a weakly connected two-world countermodel with distinct SCCs. Conditions
are local to the universal clause, not metaphysical premises. -/
def Certificate : Prop :=
  (∀ (World : Type u) (F : Frame World), Reflexive F → Symmetric F → Transitive F →
    ∀ a b,
      @Quiver.StronglyConnectedComponent.mk World F.toQuiver a =
        @Quiver.StronglyConnectedComponent.mk World F.toQuiver b ↔ F.access a b) ∧
  ((∀ a b : Bool,
      @Quiver.WeaklyConnectedComponent.mk Bool oneWay.toQuiver a =
        @Quiver.WeaklyConnectedComponent.mk Bool oneWay.toQuiver b) ∧
    @Quiver.StronglyConnectedComponent.mk Bool oneWay.toQuiver false ≠
      @Quiver.StronglyConnectedComponent.mk Bool oneWay.toQuiver true)

end TruthCore.Modal.AccessibilityComponents
