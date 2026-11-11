module

public import TruthCore.Results.Comparison.NaturalisticRealism.ModelFacts

@[expose] public section

namespace TruthCore.Results.Comparison.NaturalisticRealism.RailtonAscriptionConsistent
open TruthCore.Comparison.NaturalisticRealism

theorem railtonAscriptionConsistent : RailtonAscriptionConsistent := by
  refine ⟨model, modelRailton, ?_, ?_, ?_⟩
  · exact ⟨false, true, false, rfl, trivial, trivial, trivial, Bool.noConfusion⟩
  · exact ⟨false, true, rfl, trivial, rfl⟩
  · refine ⟨false, true, rfl, ?_⟩
    intro h
    have impossible : (false : Bool) = true := h.1
    cases impossible

end TruthCore.Results.Comparison.NaturalisticRealism.RailtonAscriptionConsistent
