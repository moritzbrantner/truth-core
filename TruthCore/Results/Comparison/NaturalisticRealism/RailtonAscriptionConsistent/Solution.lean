import TruthCore.Results.Comparison.NaturalisticRealism.ModelFacts
namespace TruthCore.Results.Comparison.NaturalisticRealism.RailtonAscriptionConsistent
open TruthCore.Comparison.NaturalisticRealism

theorem railtonAscriptionConsistent : RailtonAscriptionConsistent := by
  refine ⟨model, modelRailton, ?_, ?_, ?_⟩
  · exact ⟨false, true, false, rfl, trivial, trivial, trivial, Bool.noConfusion⟩
  · exact ⟨false, true, rfl, trivial, rfl⟩
  · exact ⟨false, true, rfl, id⟩

end TruthCore.Results.Comparison.NaturalisticRealism.RailtonAscriptionConsistent
