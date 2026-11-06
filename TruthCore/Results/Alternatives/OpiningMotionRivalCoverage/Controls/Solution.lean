module

public import TruthCore.Results.Alternatives.OpiningMotionRivalCoverage.CounterFailure.Solution

@[expose] public section
namespace TruthCore.Results.Alternatives.OpiningMotionRivalCoverage.Controls
open TruthCore.Alternatives.OpiningMotionRivalCoverage
open TruthCore.Alternatives.ActPotencyRegress

/-- Analyst matching-scope rival consequence; original motion/retorsion results stay fixed. -/
theorem controls : Controls := by
  have hCounter : Countertuple mixedMoved mixedOpinions mixedRespect := by
    refine ⟨false, True, rfl, ?_⟩
    intro h
    cases h
  refine ⟨?_, ⟨true, (), rfl⟩, hCounter, ?_, ?_⟩
  · refine ⟨false, true, True, ?_, rfl, ?_, rfl⟩
    · intro h; cases h
    · intro r h; cases h
  · intro h
    exact h.1 true () rfl
  · exact TruthCore.Results.Alternatives.OpiningMotionRivalCoverage.CounterFailure.counterFailure
      mixedMoved mixedOpinions mixedRespect hCounter

end TruthCore.Results.Alternatives.OpiningMotionRivalCoverage.Controls
