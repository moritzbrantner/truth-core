import TruthCore.Results.Comparison.NaturalisticRealism.ModelFacts
namespace TruthCore.Results.Comparison.NaturalisticRealism.RailtonConsistent
open TruthCore.Metaethics.NaturalisticRealism
open TruthCore.Comparison.NaturalisticRealism

theorem railtonConsistent : RailtonConsistent := by
  refine ⟨model, ?_, ?_, ?_, ?_⟩
  · exact modelRailton
  · exact ⟨false, true, trivial, trivial, trivial, Bool.noConfusion⟩
  · exact ⟨false, true, rfl, id⟩
  · exact ⟨false, trivial, rfl⟩

end TruthCore.Results.Comparison.NaturalisticRealism.RailtonConsistent
