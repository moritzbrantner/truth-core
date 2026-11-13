import TruthCore.Case.Catholicism.PossessionConsumerReductions

namespace TruthCore.Results.Case.Catholicism.PossessionConsumerReductions
open TruthCore.Case.Catholicism.PreexistenceWithoutTransfer
open TruthCore.Causality.CausalMapsBatch1
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.InMetaphysicam
open TruthCore.Logic

theorem nothingMovesExceptInAct {B R : Type} (MovesIn CausesIn : B → B → R → Prop)
    (InAct : B → R → Prop) (PartOf : B → B → Prop)
    (hEM : ExcludedMiddle)
    (hCause : MoverCausesWhatItMovesTo MovesIn CausesIn)
    (hHas : DistinctCauseHasWhatItGives CausesIn InAct)
    (hSelf : SelfMoverMovesByADistinctPart MovesIn PartOf)
    (hWhole : WholeInActThroughItsPart PartOf InAct) :
    MovesOnlyAsInActReading MovesIn InAct := by
  sorry

theorem gradesHaveAMaximum {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (hBearer : MoreSuchHasThePerfectionReading InAct MoreIn)
    (hCause : DistinctCauseHasWhatItGives CausesIn InAct)
    (hExceeded : ExceededPerfectionIsCausedReading InAct MoreIn CausesIn)
    (hRegress : NoInfiniteRegressOfCausesOfAPerfectionReading CausesIn)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    GradesByApproachToAMaximumReading InAct MoreIn := by
  sorry

end TruthCore.Results.Case.Catholicism.PossessionConsumerReductions
