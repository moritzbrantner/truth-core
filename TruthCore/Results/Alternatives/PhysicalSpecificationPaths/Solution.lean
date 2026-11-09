module
public import TruthCore.Alternatives.PhysicalSpecificationPaths

@[expose] public section
namespace TruthCore.Results.Alternatives.PhysicalSpecificationPaths
open FirstOrder TruthCore.Alternatives.PhysicalSpecification

theorem embedding : embeddingControl := by
  intro L v P I D m p a t h
  obtain ⟨hne, f, hf⟩ := h
  exact ⟨hne, .firstOrder f, hf⟩

theorem specialization : specializationControl := by
  intro L v P D p a t
  rfl

theorem paths : pathControl := by
  refine ⟨.step rfl (.step rfl (.refl 2)), ?_, ?_⟩
  · decide
  · intro h
    cases h with
    | step h _ => exact h

theorem varying : varyingControl := by
  refine ⟨⟨false, trivial⟩, .firstOrder
    ((Language.Term.var (Sum.inl ())).equal (Language.Term.var (Sum.inr ⟨(), trivial⟩))), ?_⟩
  intro b _ x
  rfl

theorem correspondence : correspondenceControl := by
  intro i j x y h
  rcases h with h | h
  · exact ⟨fun _ => h.2, fun _ => h.1⟩
  · exact ⟨fun hx => False.elim (h.1 hx), fun hy => False.elim (h.2 hy)⟩

private theorem appendPath {D : Type} {r : D → D → Prop} {x y z : D}
    (h : Path r x y) (k : Path r y z) : Path r x z := by
  induction h with
  | refl => exact k
  | step e _ ih => exact .step e (ih k)

theorem reachVarying : reachVaryingControl := by
  refine ⟨⟨false, trivial⟩, .reach ⟨Link.edge, trivial⟩ (Sum.inr ⟨(), trivial⟩) (Sum.inl ()), ?_⟩
  intro b _ x
  change Path (adjacency b) (reachAnchor b) x ↔ True
  constructor
  · intro _; trivial
  · intro _
    cases b with
    | false =>
      induction x with
      | zero => exact .refl 0
      | succ n ih => exact appendPath ih (.step rfl (.refl (n + 1)))
    | true =>
      cases x with
      | false => exact .refl false
      | true => exact .step (by change false ≠ true; decide) (.refl true)

theorem rootIndependence : rootIndependenceControl :=
  ⟨reachVarying, (fun h => h), (fun h => h)⟩

theorem correspondenceFailure : correspondenceFailureControl := by
  intro h
  have bad := (h true true false true trivial).mp rfl
  cases bad

end TruthCore.Results.Alternatives.PhysicalSpecificationPaths
