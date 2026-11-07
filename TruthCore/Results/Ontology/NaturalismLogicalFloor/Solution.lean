module

public import TruthCore.Ontology.NaturalismLogicalFloor
public import TruthCore.Results.Logic.TruthPilot.LogicalFloor.Solution
public import TruthCore.Results.Ontology.Naturalism.N1EntailsN2.Solution

@[expose] public section
namespace TruthCore.Results.Ontology.NaturalismLogicalFloor
open TruthCore.Ontology.NaturalismLogicalFloor
open TruthCore.Results.Ontology.Naturalism.Survivor

theorem matchedFloor (hEM : TruthCore.Logic.ExcludedMiddle) : MatchedFloorControl := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hEM, ?_, ?_, ?_⟩
  · intro x hx; exact ⟨(), hx⟩
  · intro x hx; exact ⟨.part 0, hx, part_ne_two 0⟩
  · intro x hx; exact ⟨rfl, hx⟩
  · exact TruthCore.Results.Ontology.Naturalism.N1EntailsN2.n1EntailsN2
      ontic _ _ () (fun _ hx => ⟨rfl, hx⟩)
  · rintro x ⟨y, n, rfl, _⟩; exact ⟨rfl, part_ne_two _⟩
  · rintro x y ⟨n, rfl, _⟩ _; exact ⟨rfl, part_ne_two _⟩
  · intro Being Respect P x r
    exact TruthCore.Results.Logic.TruthPilot.LogicalFloor.nonContradiction (P x r)
  · exact ⟨.part 0, .part 0, rfl, rfl⟩
  · exact ⟨.part 0, .part 0, ⟨rfl, rfl⟩, part_ne_two 0,
      ⟨(), part_ne_two 0⟩, rfl, part_ne_two 0⟩
  · rintro a p ⟨rfl, _⟩
    exact ⟨part_ne_two 0, ⟨(), part_ne_two 0⟩, rfl, part_ne_two 0⟩
end TruthCore.Results.Ontology.NaturalismLogicalFloor
