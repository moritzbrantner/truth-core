import TruthCore.Results.Case.Catholicism.StageTwo.GodIsImmutable.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityEternity
namespace TruthCore.Results.Case.Catholicism.StageTwo.GodIsEternal
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
theorem godIsEternal {Being : Type} {Respect : Type}
    (IsGod Eternal : Being → Prop) (InPotency InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect)
    (PriorSimply : Being → Being → Prop)
    (hMaximal : GodIsMaximalInBeing IsGod InAct MoreIn esse)
    (hFirstBeing : MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply)
    (hPrior : ActSimplyPriorToPotencyReading InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hEternity : ImmutableIsEternalReading InPotency Eternal) :
    GodIsEternal IsGod Eternal := by
  sorry
end TruthCore.Results.Case.Catholicism.StageTwo.GodIsEternal
