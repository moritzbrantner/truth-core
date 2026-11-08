module
public import TruthCore.Science.FineTuningSelection
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
@[expose] public section
namespace TruthCore.Results.Science.FineTuningSelection
open TruthCore.Science.FineTuningSelection

theorem direction : CalibrationDirection := by
  intro d n h
  have hn : 0 < likelihood n := div_pos n.evidence_pos n.observers_pos
  have hlt : likelihood n < likelihood d := by
    rcases h with ⟨hd, hn'⟩
    linarith
  change 1 < likelihood d / likelihood n
  apply (lt_div_iff₀ hn).2
  simpa using hlt

theorem controls : SelectionControls := by
  norm_num [SelectionControls, Calibrated, factor, likelihood, design,
    natural, selectedNatural, indifferentDesigner]
end TruthCore.Results.Science.FineTuningSelection
