import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.AdoptedPotency
namespace TruthCore.Results.Aquinas.SummaTheologiae.AdoptedPotencyNonOverlap
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- F1 entails non-overlap for the adopted capacity-without-act definition only. -/
theorem nonOverlap {Being Respect : Type} (InAct CanBe : Being → Respect → Prop)
    (hF1 : TruthCore.Logic.CaseNonContradiction.CasePredicateNonContradiction.{1, 1}) :
    AdoptedPotency.NonOverlap InAct CanBe := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.AdoptedPotencyNonOverlap
