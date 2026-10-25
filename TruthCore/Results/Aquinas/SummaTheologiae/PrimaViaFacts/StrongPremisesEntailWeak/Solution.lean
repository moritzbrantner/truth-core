import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3Interpretation
namespace TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFacts.StrongPremisesEntailWeak
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- In every motion model the strong-reading premises entail the weaker-reading
premises: the per se link of the strong reading covers the relevant-respect
case. No premises. -/
theorem strongPremisesEntailWeakPremises : StrongPremisesEntailWeakPremises :=
  by
  intro M ⟨hSense, hPotency, hAct, hReduction, hNotBoth, hPerSe, hRegress⟩
  exact ⟨hSense, hPotency, hAct, hReduction, hNotBoth,
    fun y x r r' hDistinct hMoves hMoved _ => hPerSe y x r hDistinct hMoves ⟨r', hMoved⟩,
    hRegress⟩

end TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFacts.StrongPremisesEntailWeak
