module
public import TruthCore.Causality.HistoricalRemoval
@[expose] public section
namespace TruthCore.Results.Causality.HistoricalRemoval
open TruthCore.Causality.HistoricalRemoval


theorem comparison : Comparison := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B p hi hl hd y x h
    have ht := (hi y x h).2
    have hf := (hl y x (hd y x h)).2
    exact Bool.noConfusion (ht.symm.trans hf)
  · unfold Temporal Independent Loss Dictionary sample
    decide
  · unfold Temporal Independent Loss Dictionary sample
    decide
  · unfold Temporal Independent Loss Dictionary sample
    decide
end TruthCore.Results.Causality.HistoricalRemoval
