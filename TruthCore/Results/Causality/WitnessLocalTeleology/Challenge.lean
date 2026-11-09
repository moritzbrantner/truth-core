import TruthCore.Causality.WitnessLocalTeleology

namespace TruthCore.Results.Causality.WitnessLocalTeleology
open TruthCore.Causality.WitnessLocalTeleology
open TruthCore.Causality.TeleologyFirstMover.Control hiding Controls
open TruthCore.Latin.Aquinas.SummaTheologiae TruthCore.Case.Catholicism
open TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels
theorem weaken {B R E : Type} (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Body Cog Intel : B → Prop) (Reg Best Chance Tends : B → E → Prop)
    (Dir : B → B → E → Prop)
    (h : Universal Moved Moves Body Cog Intel Reg Best Chance Tends Dir) :
    Bundle Moved Moves Body Cog Intel Reg Best Chance Tends Dir := by
  sorry

theorem firstMover {B R E : Type} (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Body Cog Intel : B → Prop) (Reg Best Chance Tends : B → E → Prop)
    (Dir : B → B → E → Prop)
    (h : Bundle Moved Moves Body Cog Intel Reg Best Chance Tends Dir) :
    ThereIsAFirstUnmovedMover Moved Moves := by
  sorry
theorem pack {Being : Type} {Respect : Type} {End : Type}
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
    Universal MovedIn MovesIn NaturalBody HasCognition Intelligent RegularlyAttains Best ByChance TendsTo Directs := by
  sorry

deriving instance DecidableEq for W

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 100000 in
theorem controls : TruthCore.Causality.WitnessLocalTeleology.Controls := by
  sorry
end TruthCore.Results.Causality.WitnessLocalTeleology
