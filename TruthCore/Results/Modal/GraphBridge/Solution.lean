import TruthCore.Modal.GraphBridge

namespace TruthCore.Results.Modal.GraphBridge
open TruthCore.Modal

universe u v

/-- Frame-to-digraph-to-frame is a structural roundtrip. -/
theorem frame_roundtrip {World : Type u} (F : Frame World) :
    Frame.ofDigraph F.toDigraph = F := by
  rfl

/-- Digraph-to-frame-to-digraph is a structural roundtrip. -/
theorem digraph_roundtrip {World : Type u} (G : Digraph World) :
    (Frame.ofDigraph G).toDigraph = G := by
  rfl

/-- Directed one-step adjacency, including loops, is unchanged. -/
theorem adjacency_iff_access {World : Type u} (F : Frame World) (a b : World) :
    F.toDigraph.Adj a b ↔ F.access a b := by
  exact Iff.rfl

/-- The explicit quiver has an arrow exactly for an original accessibility edge. -/
theorem arrow_iff_access {World : Type u} (F : Frame World) (a b : World) :
    Nonempty (@Quiver.Hom World F.toQuiver a b) ↔ F.access a b := by
  constructor
  · rintro ⟨h⟩
    exact h.down
  · intro h
    exact ⟨⟨h⟩⟩

/-- The lifted proof-valued edge type has no distinguishable parallel arrows. -/
theorem quiver_is_thin {World : Type u} (F : Frame World) :
    @Quiver.IsThin World F.toQuiver := by
  intro a b
  change Subsingleton (PLift (F.access a b))
  infer_instance

/-- Mathlib quiver reachability is precisely the reflexive-transitive closure
of directed accessibility, not one-step accessibility on an arbitrary frame. -/
theorem reachable_iff_reflTransGen {World : Type u} (F : Frame World) (a b : World) :
    @Quiver.Reachable World F.toQuiver a b ↔ Relation.ReflTransGen F.access a b := by
  let := F.toQuiver
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact Relation.ReflTransGen.refl
    | cons p e ih => exact Relation.ReflTransGen.tail ih e.down
  · intro h
    induction h with
    | refl => exact ⟨Quiver.Path.nil⟩
    | tail _ hEdge ih =>
        obtain ⟨p⟩ := ih
        exact ⟨p.cons ⟨hEdge⟩⟩

/-- Reachability equals accessibility only under the explicit reflexivity and
transitivity hypotheses, which allow reuse of Mathlib's closure theorem. -/
theorem reachable_iff_access {World : Type u} (F : Frame World)
    (hRefl : TruthCore.Modal.Reflexive F) (hTrans : TruthCore.Modal.Transitive F)
    (a b : World) :
    @Quiver.Reachable World F.toQuiver a b ↔ F.access a b := by
  let : Std.Refl F.access := ⟨hRefl⟩
  let : IsTrans World F.access := ⟨hTrans⟩
  rw [reachable_iff_reflTransGen F a b, Relation.reflTransGen_eq_self]

/-- K4 box persistence along paths, including nil paths. The conclusion remains
a box; truth of the unboxed formula at a nil endpoint would need reflexivity. -/
theorem box_along_paths {World : Type u} {Atom : Type v} (F : Frame World)
    (hTrans : TruthCore.Modal.Transitive F) (V : Valuation World Atom)
    (φ : Formula Atom) (a b : World)
    (hPath : @Quiver.Reachable World F.toQuiver a b)
    (hBox : Holds F V a (.box φ)) : Holds F V b (.box φ) := by
  let := F.toQuiver
  obtain ⟨p⟩ := hPath
  induction p with
  | nil => exact hBox
  | cons p e ih => exact axiom4_valid F hTrans φ V _ ih _ e.down

/-- K45 gives the same successor cone at any accessible world, pointwise.
This supports later scope transport without assuming global world identity. -/
theorem successor_cones {World : Type u} (F : Frame World)
    (hTrans : TruthCore.Modal.Transitive F) (hEucl : TruthCore.Modal.Euclidean F)
    (a b : World) (hab : F.access a b) :
    ∀ c, F.access a c ↔ F.access b c := by
  intro c
  exact ⟨fun hac => hEucl a b c hab hac, fun hbc => hTrans a b c hab hbc⟩

/-- A dead-end frame still has a nil path. Box-false holds there, but fails if
one silently replaces one-step access with reflexive-transitive closure. The
closure frame appears only in this control, never as the adapter semantics. -/
theorem nil_path_boundary :
    let F : Frame Unit := ⟨fun _ _ => False⟩
    let V : Valuation Unit Unit := fun _ _ => False
    @Quiver.Reachable Unit F.toQuiver () () ∧
      (¬ F.access () ()) ∧ Holds F V () (.box .falsum) ∧
      ¬ Holds (⟨Relation.ReflTransGen F.access⟩ : Frame Unit) V () (.box .falsum) := by
  let F : Frame Unit := ⟨fun _ _ => False⟩
  let := F.toQuiver
  refine ⟨⟨Quiver.Path.nil⟩, ?_, ?_, ?_⟩
  · exact fun h => h
  · intro x h
    exact h
  · intro h
    exact h () Relation.ReflTransGen.refl

end TruthCore.Results.Modal.GraphBridge
