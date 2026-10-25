import TruthCore.Results.Comparison.NaturalisticRealism.ModelFacts
namespace TruthCore.Results.Comparison.NaturalisticRealism.BoydAscriptionConsistent
open TruthCore.Comparison.NaturalisticRealism

theorem boydAscriptionConsistent : BoydAscriptionConsistent := by
  refine ⟨model, modelBoyd, ?_, ?_, ?_⟩
  · exact ⟨false, true, false, rfl, trivial, trivial, trivial, Bool.noConfusion⟩
  · exact ⟨false, true, rfl, trivial, rfl⟩
  · exact ⟨false, true, rfl, id⟩

end TruthCore.Results.Comparison.NaturalisticRealism.BoydAscriptionConsistent
