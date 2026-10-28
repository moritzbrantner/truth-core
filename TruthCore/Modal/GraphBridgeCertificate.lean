import TruthCore.Modal.GraphBridge

/-! A transparent assembly target for the reusable graph bridge helpers.
Every frame restriction stays inside its own quantified clause. This bundles
existing helper conclusions for delivery; it is not a new philosophical proof.
-/
namespace TruthCore.Modal
universe u v

/-- Faithful one-step adapters, their path-closure relationship, restricted
modal consequences and the dead-end boundary. No frame condition or world
population is imposed globally. See each conjunct for its exact hypotheses. -/
def GraphBridgeCertificate : Prop :=
  (∀ (World : Type u) (F : Frame World), Frame.ofDigraph F.toDigraph = F) ∧
  (∀ (World : Type u) (G : Digraph World), (Frame.ofDigraph G).toDigraph = G) ∧
  (∀ (World : Type u) (F : Frame World) a b, F.toDigraph.Adj a b ↔ F.access a b) ∧
  (∀ (World : Type u) (F : Frame World) a b,
    Nonempty (@Quiver.Hom World F.toQuiver a b) ↔ F.access a b) ∧
  (∀ (World : Type u) (F : Frame World), @Quiver.IsThin World F.toQuiver) ∧
  (∀ (World : Type u) (F : Frame World) a b,
    @Quiver.Reachable World F.toQuiver a b ↔ Relation.ReflTransGen F.access a b) ∧
  (∀ (World : Type u) (F : Frame World), Reflexive F → Transitive F → ∀ a b,
    @Quiver.Reachable World F.toQuiver a b ↔ F.access a b) ∧
  (∀ (World : Type u) (Atom : Type v) (F : Frame World), Transitive F →
    ∀ (V : Valuation World Atom) (φ : Formula Atom) a b,
    @Quiver.Reachable World F.toQuiver a b → Holds F V a (.box φ) →
      Holds F V b (.box φ)) ∧
  (∀ (World : Type u) (F : Frame World), Transitive F → Euclidean F →
    ∀ a b, F.access a b → ∀ c, F.access a c ↔ F.access b c) ∧
  (let F : Frame Unit := ⟨fun _ _ => False⟩
   let V : Valuation Unit Unit := fun _ _ => False
   @Quiver.Reachable Unit F.toQuiver () () ∧
     (¬ F.access () ()) ∧ Holds F V () (.box .falsum) ∧
     ¬ Holds (⟨Relation.ReflTransGen F.access⟩ : Frame Unit) V () (.box .falsum))

end TruthCore.Modal
