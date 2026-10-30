import TruthCore.Alternatives.NightActualizationFork

namespace TruthCore.Results.Alternatives.NightActualizationFork
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Alternatives.NightCosmogony
open TruthCore.Alternatives.NightActualizationFork

/-- Coverage at one Night witness, with excluded middle explicit. Either it has
no actual mover, it is an actual self-mover, or a distinct actual mover moves it
without simple priority. The alternatives need not be exclusive. -/
theorem coverage {Being Respect : Type}
    (InAct InPotency MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop)
    (hNight : UnprecededPotencyActualizedReading InAct InPotency MovedIn PriorSimply)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    NightActualizationFork InAct InPotency MovedIn MovesIn PriorSimply := by
  sorry

/-- The root mover premises exclude the no-actual-mover and actual-self-mover
repairs constructively. The same Night witness has a distinct actual mover
without simple priority; no priority bridge or excluded middle is assumed. -/
theorem forcedOtherFromRootPremises {Being Respect : Type}
    (InAct InPotency MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop)
    (hNight : UnprecededPotencyActualizedReading InAct InPotency MovedIn PriorSimply)
    (hHasMover : ReducedOnlyByAMoverReading MovedIn MovesIn)
    (hMoverInAct : MovesOnlyAsInActReading MovesIn InAct)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency) :
    NightNonpriorOtherActualMover InAct InPotency MovedIn MovesIn PriorSimply := by
  sorry

end TruthCore.Results.Alternatives.NightActualizationFork
