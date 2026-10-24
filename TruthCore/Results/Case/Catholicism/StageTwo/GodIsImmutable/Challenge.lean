import TruthCore.Results.Case.Catholicism.StageTwo.GodIsPerfect.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
namespace TruthCore.Results.Case.Catholicism.StageTwo.GodIsImmutable
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
theorem godIsImmutable {Being : Type} {Respect : Type}
    (IsGod : Being → Prop) (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InPotency InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hMaximal : GodIsMaximalInBeing IsGod InAct MoreIn esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hReduction : ReducedOnlyByAMoverReading MovedIn MovesIn)
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn InPotency)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency) :
    GodIsImmutable IsGod (IsImmutable MovedIn) := by
  sorry
end TruthCore.Results.Case.Catholicism.StageTwo.GodIsImmutable
