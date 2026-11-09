module
public import TruthCore.Causality.ConceptualExistenceBoundary
@[expose] public section
namespace TruthCore.Results.Causality.ConceptualExistenceBoundary
open TruthCore.Causality.ConceptualExistenceBoundary

theorem existingExemplar {C F : Type} (m : Interpretation C F) (c : C)
    (hTransfer : Transfer m c) (hAnchor : Anchor m)
    (hExists : ActualityExists m) : ExistingExemplar m := by
  obtain ⟨f, hn, ha⟩ := hAnchor
  exact ⟨c, hExists c (ha c (hTransfer f hn)), hTransfer⟩

theorem controls : Controls := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨(fun _ _ => True.intro), ⟨true, rfl, fun _ _ => True.intro⟩,
      (fun _ _ => True.intro), ⟨(), True.intro, fun _ _ => True.intro⟩⟩
  · exact ⟨(fun h => h true rfl), ⟨true, rfl, fun _ h => h.elim⟩,
      (fun _ h => h.elim), fun ⟨_, h, _⟩ => h⟩
  · exact ⟨(fun _ _ => True.intro), (fun ⟨_, _, h⟩ => h () True.intro),
      (fun _ h => h.elim), fun ⟨_, h, _⟩ => h⟩
  · exact ⟨(fun _ _ => True.intro), ⟨true, rfl, fun _ _ => True.intro⟩,
      (fun h => h () True.intro), fun ⟨_, h, _⟩ => h⟩
end TruthCore.Results.Causality.ConceptualExistenceBoundary
