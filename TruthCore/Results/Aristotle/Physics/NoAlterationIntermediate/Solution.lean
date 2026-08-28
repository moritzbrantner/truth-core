import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter2
namespace TruthCore.Results.Aristotle.Physics.NoAlterationIntermediate
open TruthCore.Greek.Aristotle.Physics
theorem noAlterationIntermediate
    (LastAltererAndFirstAlteredAdjacent NothingBetweenAltererAndAltered : Prop)
    (hAdjacent : SensibleAlterationExtremesAdjacentThroughMediaReading
      LastAltererAndFirstAlteredAdjacent)
    (hTransition : AlterationAdjacencyEntailsNoIntermediateReading
      LastAltererAndFirstAlteredAdjacent NothingBetweenAltererAndAltered) :
    NoIntermediateBetweenAltererAndAlteredReading
      NothingBetweenAltererAndAltered := by
  exact hTransition hAdjacent
end TruthCore.Results.Aristotle.Physics.NoAlterationIntermediate
