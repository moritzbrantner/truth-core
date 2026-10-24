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
  -- CATHOLICISM-STAGE2-GOD-IS-PERFECT (imported)
  have hPerfect := TruthCore.Results.Case.Catholicism.StageTwo.GodIsPerfect.godIsPerfect IsGod
    InAct MoreIn CausesIn esse hMaximal hGenus hBeing hPreexist hEM
  -- INF-STAGE2-GOD-IS-IMMUTABLE (q.9 a.1, first and third reasons): were God moved in r,
  -- a mover in act in r would move him, so God (perfect) would be in act in r, and,
  -- being moved in r, in potency in r
  intro g hg r hMoved
  obtain ⟨y, hMoves⟩ := hReduction g r hMoved
  exact hNotBoth g r ⟨hPerfect g hg y r (hAct y g r hMoves), hPotency g r hMoved⟩

end TruthCore.Results.Case.Catholicism.StageTwo.GodIsImmutable
