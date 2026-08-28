import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter2
namespace TruthCore.Results.Aristotle.Physics.NoLocalMoverIntermediate
open TruthCore.Greek.Aristotle.Physics
theorem noLocalMoverIntermediate
    (SelfMoved MovedByOther Pulling Pushing Carrying Twirling
      NothingBetweenMoverAndMoved : Prop)
    (hCases : LocomotionSelfMovedOrMovedByOtherReading SelfMoved MovedByOther)
    (hSelf : SelfMovedLocomotionHasNoIntermediateReading
      SelfMoved NothingBetweenMoverAndMoved)
    (hModes : ExternalLocomotionHasFourModesReading
      MovedByOther Pulling Pushing Carrying Twirling)
    (hExternal : ExternalLocomotionModesEntailNoIntermediateReading
      Pulling Pushing Carrying Twirling NothingBetweenMoverAndMoved) :
    NoIntermediateBetweenLocalMoverAndMovedReading
      NothingBetweenMoverAndMoved := by
  sorry
end TruthCore.Results.Aristotle.Physics.NoLocalMoverIntermediate
