module

public import TruthCore.Results.Comparison.NaturalisticRealism.ModelFacts

@[expose] public section

namespace TruthCore.Results.Comparison.NaturalisticRealism.BoydConsistent
open TruthCore.Metaethics.NaturalisticRealism
open TruthCore.Comparison.NaturalisticRealism

theorem boydConsistent : BoydConsistent := by
  refine ⟨model, ?_, ?_, ?_, ?_⟩
  · exact modelBoyd
  · exact ⟨false, true, trivial, trivial, trivial, Bool.noConfusion⟩
  · refine ⟨false, true, rfl, ?_⟩
    intro h
    have impossible : (false : Bool) = true := h.1
    cases impossible
  · exact ⟨false, trivial, rfl⟩

end TruthCore.Results.Comparison.NaturalisticRealism.BoydConsistent
