import TruthCore.Metaethics.DescriptivePlanBoundary
namespace TruthCore.Results.Metaethics.DescriptivePlanBoundary
open TruthCore.Metaethics.DescriptivePlanBoundary
open TruthCore.Metaethics.PlanStateEmbedding
/-- Exact stipulated semantic boundary; no substantive moral truth is inferred. -/
theorem boundary : Boundary := by
  refine ⟨?_, ?_, ?_⟩
  · intro Fact Action theory hd hs
    obtain ⟨w, hw⟩ := hs
    let v : Point Fact Action := ⟨w.factual, fun _ => true⟩
    refine ⟨v, ?_, fun _ => rfl⟩
    intro p hp
    exact (descriptiveSupport p (hd p hp) w v rfl).mp (hw p hp)
  · intro Fact Action state f a hf hc
    exact TruthCore.Results.Metaethics.PlanStateEmbeddingControl.planStateEmbeddingControl.1
      Fact Action state (.factual f) (.forbidden a) hf hc
  · let w : Point Unit ExampleAction := ⟨fun _ => true, fun _ => true⟩
    refine ⟨{w}, ⟨w, rfl⟩, ?_, ?_, ?_, ?_⟩
    · intro v hv
      cases hv
      rfl
    · intro v hv
      cases hv
      rfl
    · intro h
      have bad : true = false := h (show w ∈ ({w} : Set (Point Unit ExampleAction)) from rfl)
      cases bad
    · intro h
      rcases h (show w ∈ ({w} : Set (Point Unit ExampleAction)) from rfl) with hn | hq
      · exact hn rfl
      · have bad : true = false := hq
        cases bad
end TruthCore.Results.Metaethics.DescriptivePlanBoundary
