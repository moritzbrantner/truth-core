import TruthCore.Causality.TeleologyFirstMover

namespace TruthCore.Results.Causality.TeleologyFirstMover
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Results.Aquinas.SummaTheologiae
open TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels
open TruthCore.Causality.TeleologyFirstMover.Control

theorem firstMover {Being : Type} {Respect : Type} {End : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (NaturalBody HasCognition Intelligent : Being → Prop)
    (RegularlyAttains Best ByChance TendsTo : Being → End → Prop)
    (Directs : Being → Being → End → Prop)
    (hLack : NaturalBodiesLackCognitionReading NaturalBody HasCognition)
    (hObs : NaturalBodiesActRegularlyForTheBestReading NaturalBody RegularlyAttains Best)
    (hNotChance : RegularityIsNotByChanceReading RegularlyAttains ByChance)
    (hDich : RegularBestByChanceOrByIntentionReading RegularlyAttains Best ByChance TendsTo)
    (hArrow : NonCognitiveTendingNeedsKnowingDirectorReading HasCognition Intelligent
      TendsTo Directs)
    (hReduce : NaturalDirectionReducedToIntelligentImmobileDirector MovedIn NaturalBody
      HasCognition Intelligent Directs)
    (hMoving : DirectingIsMoving MovesIn Directs)
 :
    ThereIsAFirstUnmovedMover MovedIn MovesIn := by
  sorry

theorem governorProjects {B R E : Type} (Moved : B → R → Prop)
    (Moves : B → B → R → Prop) (Body Intelligent : B → Prop)
    (Directs : B → B → E → Prop)
    (h : OneIntelligentFirstMoverGovernsNature Moved Moves Body Intelligent Directs) :
    ThereIsAFirstUnmovedMover Moved Moves := by
  sorry

theorem controls : Controls := by
  sorry
end TruthCore.Results.Causality.TeleologyFirstMover
