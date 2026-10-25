import TruthCore.Logic.TruthPilot
namespace TruthCore.Results.Logic.TruthPilot.GlobalVariation
open TruthCore.Logic.TruthPilot
/-- A globally variable interpretation exists when no logical-sentence stability bridge is imposed. A countermodel to any unconditional self-refutation inference from that bare definition. -/
theorem globalVariation : GlobalVariationModelExists := by
  let Holds : Interpretation := fun E s => E Agent.first s
  refine ⟨Holds, ?_⟩
  intro s
  refine ⟨(fun _ _ => True), (fun _ _ => False), ?_, ?_⟩
  · trivial
  · intro h
    exact h
end TruthCore.Results.Logic.TruthPilot.GlobalVariation
