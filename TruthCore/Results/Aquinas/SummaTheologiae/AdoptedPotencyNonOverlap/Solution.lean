module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.AdoptedPotency

@[expose] public section

namespace TruthCore.Results.Aquinas.SummaTheologiae.AdoptedPotencyNonOverlap
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- F1 entails non-overlap for the adopted capacity-without-act definition only. -/
theorem nonOverlap {Being Respect : Type} (InAct CanBe : Being → Respect → Prop)
    (hF1 : TruthCore.Logic.CaseNonContradiction.CasePredicateNonContradiction.{1, 1}) :
    AdoptedPotency.NonOverlap InAct CanBe :=
  AdoptedPotency.nonOverlap InAct CanBe hF1
end TruthCore.Results.Aquinas.SummaTheologiae.AdoptedPotencyNonOverlap
