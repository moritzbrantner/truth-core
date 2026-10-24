import TruthCore.Case.Catholicism.StageTwo
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1
namespace TruthCore.Results.Case.Catholicism.StageTwo.GodIsImmutable
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
theorem godIsImmutable {Being : Type} {Respect : Type}
    (IsGod : Being → Prop) (InPotency InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect)
    (PriorSimply : Being → Being → Prop)
    (hMaximal : GodIsMaximalInBeing IsGod InAct MoreIn esse)
    (hFirstBeing : MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply)
    (hPureAct : FirstBeingIsInNoWayInPotencyReading InPotency PriorSimply) :
    GodIsImmutable IsGod (IsImmutable InPotency) := by
  sorry
end TruthCore.Results.Case.Catholicism.StageTwo.GodIsImmutable
