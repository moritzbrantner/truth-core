import TruthCore.Results.Case.Catholicism.StageTwo.GodIsImmutable.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityEternity
namespace TruthCore.Results.Case.Catholicism.StageTwo.GodIsEternal
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

theorem godIsEternal {Being : Type} {Respect : Type}
    (IsGod Eternal : Being → Prop) (MovedIn : Being → Respect → Prop)
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
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hEternity : ImmutableIsEternalReading MovedIn Eternal) :
    GodIsEternal IsGod Eternal := by
  -- CATHOLICISM-STAGE2-GOD-IS-IMMUTABLE (imported)
  have hImmutable := TruthCore.Results.Case.Catholicism.StageTwo.GodIsImmutable.godIsImmutable
    IsGod MovedIn MovesIn InPotency InAct MoreIn CausesIn esse hMaximal hGenus hBeing hPreexist
    hEM hReduction hAct hPotency hNotBoth
  -- INF-STAGE2-GOD-IS-ETERNAL (q.10 a.2: eternity follows immutability)
  exact fun g hg => hEternity g (hImmutable g hg)

end TruthCore.Results.Case.Catholicism.StageTwo.GodIsEternal
