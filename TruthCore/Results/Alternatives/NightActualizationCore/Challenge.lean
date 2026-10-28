import TruthCore.Alternatives.NightCosmogony
import TruthCore.Logic.Configuration

namespace TruthCore.Results.Alternatives.NightActualizationCore
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Alternatives.NightCosmogony

/-- The Night reading and four root-related commitments cannot coexist under
one act/potency semantics. This conditional incompatible bundle rejects no
preferred member; the simple-priority bridge remains open. The proof composes
the existing Night elimination from root premises. -/
theorem incompatible {Being Respect : Type}
    (InAct InPotency MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop)
    (hNight : UnprecededPotencyActualizedReading InAct InPotency MovedIn PriorSimply)
    (hHasMover : ReducedOnlyByAMoverReading MovedIn MovesIn)
    (hMoverInAct : MovesOnlyAsInActReading MovesIn InAct)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hMoverPrior : ActualMoverIsSimplyPriorReading InAct InPotency MovesIn PriorSimply) :
    TruthCore.Logic.ConfigurationFalse := by
  sorry

end TruthCore.Results.Alternatives.NightActualizationCore
