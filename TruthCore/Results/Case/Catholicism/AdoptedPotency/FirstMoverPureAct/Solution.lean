module

public import TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverPureAct.Solution
public import TruthCore.Results.Aquinas.SummaTheologiae.AdoptedPotencyNonOverlap.Solution

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.AdoptedPotency.FirstMoverPureAct
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (FirstUnmovedMoverIsPureAct IsFirstUnmovedMover
  FirstUnmovedMoverIsFirstBeing)

/-- Adopted-potency specialization of `AQUINAS-ST-I-Q3-A1-FIRST-MOVER-PURE-ACT`. Every occurrence of the old
potency parameter, including immutability, priority and sufficiency, is uniformly
`CanBe x r ∧ ¬ InAct x r`. The generic frozen Challenge is retained. F1 supplies
non-overlap; all other original hypotheses retain their existing scope. -/
theorem firstMoverPureAct {Being : Type}
    {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (CanBe InAct : Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop)
    (hFirstBeing : FirstUnmovedMoverIsFirstBeing MovedIn MovesIn PriorSimply)
    (hPrior : ActSimplyPriorToPotencyReading InAct (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe) PriorSimply)
    (hF1 : TruthCore.Logic.CaseNonContradiction.CasePredicateNonContradiction.{1, 1}):
    FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe)) := by
  exact TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverPureAct.firstMoverPureAct
    MovedIn MovesIn (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe) InAct PriorSimply
    hFirstBeing hPrior (TruthCore.Results.Aquinas.SummaTheologiae.AdoptedPotencyNonOverlap.nonOverlap InAct CanBe hF1)
end TruthCore.Results.Case.Catholicism.AdoptedPotency.FirstMoverPureAct
