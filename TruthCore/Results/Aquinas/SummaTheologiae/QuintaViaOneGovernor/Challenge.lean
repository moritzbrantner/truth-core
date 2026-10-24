import TruthCore.Case.Catholicism.StageOneQuintaVia
import TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaOneGovernor
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels
open TruthCore.Case.Catholicism (AtMostOneFirstUnmovedMover IsFirstUnmovedMover
  OneIntelligentFirstMoverGovernsNature NaturalDirectionReducedToIntelligentImmobileDirector
  DirectingIsMoving)

/-- ST I q.2 a.3, fifth way with ad 2: the scope step. Each natural body is
directed by some knower (`QuintaViaEachDirected.eachDirected`). By the open
bridge on which ad 2 bears, its direction is reduced to an intelligent director
moved by none; by the open bridge that directing is moving, that director is a
first mover moved by none. There is at most one
such (stage 1, `AtMostOneFirstUnmovedMover`). So one intelligent first mover
directs every natural body. -/
theorem oneGovernor {Being : Type} {Respect : Type} {End : Type}
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
    (hOne : AtMostOneFirstUnmovedMover MovedIn MovesIn) :
    OneIntelligentFirstMoverGovernsNature MovedIn MovesIn NaturalBody Intelligent
      Directs := by
  sorry

/-- The derived statement entails the *quinta via*'s literal conclusion. -/
theorem entailsQuintaViaConclusion {Being : Type} {Respect : Type} {End : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (NaturalBody Intelligent : Being → Prop)
    (Directs : Being → Being → End → Prop)
    (h : OneIntelligentFirstMoverGovernsNature MovedIn MovesIn NaturalBody Intelligent
      Directs) :
    OneIntelligentDirectsAllNaturalThingsReading NaturalBody Intelligent Directs := by
  sorry

/-- The reduction bridge is needed: two archers each direct one body, and
the archers are themselves moved. Every other premise holds (uniqueness
vacuously); there is no first director and no one governor. -/
theorem withoutReduction :
    NaturalBodiesLackCognitionReading isBody isDirector ∧
    NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd ∧
    RegularityIsNotByChanceReading bodyEnd noEnd ∧
    RegularBestByChanceOrByIntentionReading bodyEnd allEnd noEnd bodyEnd ∧
    NonCognitiveTendingNeedsKnowingDirectorReading isDirector isDirector bodyEnd
      twoDirects ∧
    DirectingIsMoving twoDirects twoDirects ∧
    AtMostOneFirstUnmovedMover directorsMoved twoDirects ∧
    ¬ NaturalDirectionReducedToIntelligentImmobileDirector directorsMoved isBody isDirector
      isDirector twoDirects ∧
    ¬ OneIntelligentFirstMoverGovernsNature directorsMoved twoDirects isBody isDirector
      twoDirects := by
  sorry

/-- Directing-is-moving is needed: the two archers are moved by none and direct,
but move nothing, so they are not first movers and uniqueness does not apply. -/
theorem withoutDirectingIsMoving :
    NaturalBodiesLackCognitionReading isBody isDirector ∧
    NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd ∧
    RegularityIsNotByChanceReading bodyEnd noEnd ∧
    RegularBestByChanceOrByIntentionReading bodyEnd allEnd noEnd bodyEnd ∧
    NonCognitiveTendingNeedsKnowingDirectorReading isDirector isDirector bodyEnd
      twoDirects ∧
    NaturalDirectionReducedToIntelligentImmobileDirector nothingMoved isBody isDirector
      isDirector twoDirects ∧
    AtMostOneFirstUnmovedMover nothingMoved noMoves ∧
    ¬ DirectingIsMoving noMoves twoDirects ∧
    ¬ OneIntelligentFirstMoverGovernsNature nothingMoved noMoves isBody isDirector
      twoDirects := by
  sorry

/-- The stage-1 uniqueness premise is needed: both archers are moved by none and
move what they direct, so there are two first movers, each directing one body. -/
theorem withoutUniqueness :
    NaturalBodiesLackCognitionReading isBody isDirector ∧
    NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd ∧
    RegularityIsNotByChanceReading bodyEnd noEnd ∧
    RegularBestByChanceOrByIntentionReading bodyEnd allEnd noEnd bodyEnd ∧
    NonCognitiveTendingNeedsKnowingDirectorReading isDirector isDirector bodyEnd
      twoDirects ∧
    NaturalDirectionReducedToIntelligentImmobileDirector nothingMoved isBody isDirector
      isDirector twoDirects ∧
    DirectingIsMoving twoDirects twoDirects ∧
    ¬ AtMostOneFirstUnmovedMover nothingMoved twoDirects ∧
    ¬ OneIntelligentFirstMoverGovernsNature nothingMoved twoDirects isBody isDirector
      twoDirects := by
  sorry

/-- All premises are jointly satisfiable, non-vacuously: one governor `d0`, moved
by none, directs and moves both natural bodies. -/
theorem premisesJointlySatisfiable :
    NaturalBodiesLackCognitionReading isBody isDirector ∧
    NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd ∧
    RegularityIsNotByChanceReading bodyEnd noEnd ∧
    RegularBestByChanceOrByIntentionReading bodyEnd allEnd noEnd bodyEnd ∧
    NonCognitiveTendingNeedsKnowingDirectorReading isDirector isDirector bodyEnd
      oneDirects ∧
    NaturalDirectionReducedToIntelligentImmobileDirector nothingMoved isBody isDirector
      isDirector oneDirects ∧
    DirectingIsMoving oneDirects oneDirects ∧
    AtMostOneFirstUnmovedMover nothingMoved oneDirects := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaOneGovernor
