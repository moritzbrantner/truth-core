import TruthCore.Case.Catholicism.StageOneQuintaVia
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question103.Government
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaDirectorRegress
open TruthCore.Logic
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (NaturalDirectionReducedToIntelligentImmobileDirector)
theorem directorRegress {Being : Type} {Respect : Type} {End : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InPotency InAct : Being → Respect → Prop)
    (MovesAsMoved : Being → Being → Prop)
    (NaturalBody HasCognition Intelligent : Being → Prop)
    (Directs : Being → Being → End → Prop)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn InPotency)
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hReduction : ReducedOnlyByAMoverReading MovedIn MovesIn)
    (hPerSe : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved)
    (hEM : ExcludedMiddle)
    (hThrough : DirectionThroughIntermediariesReading MovesIn Directs)
    (hDesign : UnmovedDirectorHasTheDesignReading MovedIn HasCognition Intelligent Directs) :
    NaturalDirectionReducedToIntelligentImmobileDirector MovedIn NaturalBody HasCognition
      Intelligent Directs := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaDirectorRegress
