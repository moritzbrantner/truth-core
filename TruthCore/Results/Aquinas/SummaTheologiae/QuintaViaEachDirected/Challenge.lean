import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuintaVia
import TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaEachDirected
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels

/-- ST I q.2 a.3 co., fifth way, before the scope step: each natural body tends to
something best for it (`QuintaViaActsForAnEnd.actsForAnEnd`); natural bodies lack
cognition; and what lacks cognition tends to an end only as directed by a knower.
So each natural body is directed to something best for it by some knowing and
intelligent being. -/
theorem eachDirected {Being : Type} {End : Type}
    (NaturalBody HasCognition Intelligent : Being → Prop)
    (RegularlyAttains Best ByChance TendsTo : Being → End → Prop)
    (Directs : Being → Being → End → Prop)
    (hLack : NaturalBodiesLackCognitionReading NaturalBody HasCognition)
    (hObs : NaturalBodiesActRegularlyForTheBestReading NaturalBody RegularlyAttains Best)
    (hNotChance : RegularityIsNotByChanceReading RegularlyAttains ByChance)
    (hDich : RegularBestByChanceOrByIntentionReading RegularlyAttains Best ByChance TendsTo)
    (hArrow : NonCognitiveTendingNeedsKnowingDirectorReading HasCognition Intelligent
      TendsTo Directs) :
    EachNaturalBodyDirectedByAKnowerReading NaturalBody HasCognition Intelligent Best
      Directs := by
  sorry

/-- The arrow-and-archer premise is needed (teleonomy or immanent-teleology model):
bodies without cognition regularly attain and tend to what is best, not by
chance, and nothing directs them. -/
theorem teleonomyModel :
    NaturalBodiesLackCognitionReading isBody noneP ∧
    NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd ∧
    RegularityIsNotByChanceReading bodyEnd noEnd ∧
    RegularBestByChanceOrByIntentionReading bodyEnd allEnd noEnd bodyEnd ∧
    ¬ NonCognitiveTendingNeedsKnowingDirectorReading noneP noneP bodyEnd noDirects ∧
    ¬ EachNaturalBodyDirectedByAKnowerReading isBody noneP noneP allEnd noDirects := by
  sorry

theorem twoArchersLack : NaturalBodiesLackCognitionReading isBody isDirector := by
  sorry

theorem twoArchersArrow :
    NonCognitiveTendingNeedsKnowingDirectorReading isDirector isDirector bodyEnd
      twoDirects := by
  sorry

theorem twoArchersNoOne :
    ¬ OneIntelligentDirectsAllNaturalThingsReading isBody isDirector twoDirects := by
  sorry

/-- The naive scope step fails: every premise holds and each natural body is
directed by a knower, but two archers each direct one body, so no single
intelligent being directs all natural bodies. -/
theorem naiveScopeShiftFails :
    NaturalBodiesLackCognitionReading isBody isDirector ∧
    NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd ∧
    RegularityIsNotByChanceReading bodyEnd noEnd ∧
    RegularBestByChanceOrByIntentionReading bodyEnd allEnd noEnd bodyEnd ∧
    NonCognitiveTendingNeedsKnowingDirectorReading isDirector isDirector bodyEnd
      twoDirects ∧
    EachNaturalBodyDirectedByAKnowerReading isBody isDirector isDirector allEnd
      twoDirects ∧
    ¬ OneIntelligentDirectsAllNaturalThingsReading isBody isDirector twoDirects := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaEachDirected
