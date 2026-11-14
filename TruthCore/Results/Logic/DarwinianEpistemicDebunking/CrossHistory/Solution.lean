module

public import TruthCore.Logic.DarwinianEpistemicDebunking

/-!
The non-probabilistic part of Street's first horn (2006, pp. 121–122) for one
epistemic evaluative judgment (#1585): with the truth held fixed, a verdict
that varies with the selective history is wrong in some scenario. Street's
further step, that the actual judgments are in all likelihood mostly off
track, is probabilistic and is not encoded. Analyst formulation; attribution
deferred.
-/

@[expose] public section

namespace TruthCore.Results.Logic.DarwinianEpistemicDebunking.CrossHistory

open TruthCore.Logic.DarwinianEpistemicDebunking

theorem fixedTruthWithHistoryVariationYieldsMismatch (P : DarwinianProfile) :
    CorrectnessConstant P →
    VerdictVariesAcrossHistories P →
    ScenarioMismatch P := by
  intro hConst ⟨s, _, hVary⟩
  by_cases hActual : P.verdict P.actual = P.correct P.actual
  · refine ⟨s, ?_⟩
    rw [hConst s, ← hActual]
    exact hVary
  · exact ⟨P.actual, hActual⟩

theorem crossHistoryControls : CrossHistoryControls := by
  have hNe : false ≠ true := fun h => Bool.noConfusion h
  refine ⟨⟨fun _ => rfl, ⟨false, hNe, hNe⟩, ⟨false, hNe⟩, rfl, ?_, ?_⟩,
    ⟨fun _ => rfl, ?_, ?_⟩⟩
  · rintro ⟨s, hMate, h⟩
    change s = true at hMate
    subst hMate
    exact h rfl
  · rintro ⟨s, _, h⟩
    exact h rfl
  · rintro ⟨_, h, _⟩
    exact h rfl
  · rintro ⟨_, h⟩
    exact h rfl

end TruthCore.Results.Logic.DarwinianEpistemicDebunking.CrossHistory
