module

public import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter2

@[expose] public section

namespace TruthCore.Results.Aristotle.Physics.NoIntermediateThreeMotions
open TruthCore.Greek.Aristotle.Physics
theorem noIntermediateThreeMotions
    (NothingBetweenLocalMoverAndMoved NothingBetweenAltererAndAltered
      NothingBetweenQuantitativeMoverAndMoved : Prop)
    (hLocal : NoIntermediateBetweenLocalMoverAndMovedReading
      NothingBetweenLocalMoverAndMoved)
    (hAlteration : NoIntermediateBetweenAltererAndAlteredReading
      NothingBetweenAltererAndAltered)
    (hQuantity : NoIntermediateInGrowthOrDiminutionReading
      NothingBetweenQuantitativeMoverAndMoved) :
    NoIntermediateAcrossThreeMotionKindsReading
      NothingBetweenLocalMoverAndMoved NothingBetweenAltererAndAltered
      NothingBetweenQuantitativeMoverAndMoved := by
  exact ⟨hLocal, hAlteration, hQuantity⟩
end TruthCore.Results.Aristotle.Physics.NoIntermediateThreeMotions
