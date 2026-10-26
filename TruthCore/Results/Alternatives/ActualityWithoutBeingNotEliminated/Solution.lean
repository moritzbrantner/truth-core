import TruthCore.Alternatives.ActualityWithoutBeing
import TruthCore.Models.ActPotency
namespace TruthCore.Results.Alternatives.ActualityWithoutBeingNotEliminated
open TruthCore.Alternatives.ActualityWithoutBeing

/-- The Meinongian rival is the contradictory of ST I q.4 a.1 ad 3, and the other
act/potency premises do not refute it. No premises.

Item 3 reuses the registered omission model `M2` of #374 (`MODEL-ACT-POTENCY-M2`)
and its certified evaluations: there `a` is actually hot but not in act in `esse`,
which is a witness of the rival. -/
theorem eliminationReducesToPremise : ActualityWithoutBeingEliminationReducesToPremise := by
  refine ⟨?_, ?_, ?_⟩
  · -- rival ∧ premise ⊢ False
    intro Being Respect InAct esse hRival hPremise
    obtain ⟨x, r, hAct, hNotBeing⟩ := hRival
    exact hNotBeing (hPremise x r hAct)
  · -- refuting the rival is exactly the double-negated premise
    intro Being Respect InAct esse
    constructor
    · intro hNoRival x r hAct hNotBeing
      exact hNoRival ⟨x, r, hAct, hNotBeing⟩
    · intro hDouble hRival
      obtain ⟨x, r, hAct, hNotBeing⟩ := hRival
      exact hDouble x r hAct hNotBeing
  · -- the other seven premises, sensible motion and the regress premise hold in `M2`
    exact ⟨TruthCore.Models.ActPotency.M2.model,
      TruthCore.Models.ActPotency.M2.evaluation0,
      TruthCore.Models.ActPotency.M2.evaluation1,
      TruthCore.Models.ActPotency.M2.evaluation2,
      TruthCore.Models.ActPotency.M2.evaluation3,
      TruthCore.Models.ActPotency.M2.evaluation4,
      TruthCore.Models.ActPotency.M2.evaluation5,
      TruthCore.Models.ActPotency.M2.evaluation6,
      TruthCore.Models.ActPotency.M2.evaluation7,
      TruthCore.Models.ActPotency.M2.evaluation8,
      TruthCore.Models.ActPotency.M2.evaluation10⟩

end TruthCore.Results.Alternatives.ActualityWithoutBeingNotEliminated
