import TruthCore.Logic.DarwinianEpistemicDebunking

/-!
The non-probabilistic part of Street's first horn (2006, pp. 121–122) for one
epistemic evaluative judgment (#1585): with the truth held fixed, a verdict
that varies with the selective history is wrong in some scenario. Street's
further step, that the actual judgments are in all likelihood mostly off
track, is probabilistic and is not encoded. Analyst formulation; attribution
deferred.
-/

namespace TruthCore.Results.Logic.DarwinianEpistemicDebunking.CrossHistory

open TruthCore.Logic.DarwinianEpistemicDebunking

theorem fixedTruthWithHistoryVariationYieldsMismatch (P : DarwinianProfile) :
    CorrectnessConstant P →
    VerdictVariesAcrossHistories P →
    ScenarioMismatch P := by
  sorry

theorem crossHistoryControls : CrossHistoryControls := by
  sorry

end TruthCore.Results.Logic.DarwinianEpistemicDebunking.CrossHistory
