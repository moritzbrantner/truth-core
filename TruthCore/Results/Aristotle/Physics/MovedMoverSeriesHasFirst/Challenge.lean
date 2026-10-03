import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter1
namespace TruthCore.Results.Aristotle.Physics.MovedMoverSeriesHasFirst
open TruthCore.Greek.Aristotle.Physics
theorem movedMoverSeriesHasFirst
    (NoFirstMover InfiniteMovedMoverChain ChainFormsOneBodilyUnity
      OneUnityTraversesInfiniteMotionInFiniteTime : Prop)
    (hChain : NoFirstMoverHypothesisProducesInfiniteChainReading
      NoFirstMover InfiniteMovedMoverChain)
    (hUnity : InfiniteMovedMoverChainFormsOneUnityReading
      InfiniteMovedMoverChain ChainFormsOneBodilyUnity)
    (hTraversal : ChainUnityWouldTraverseInfiniteMotionInFiniteTimeReading
      InfiniteMovedMoverChain ChainFormsOneBodilyUnity
      OneUnityTraversesInfiniteMotionInFiniteTime)
    (hImpossible : NoInfiniteMotionInFiniteTimeReading
      OneUnityTraversesInfiniteMotionInFiniteTime) :
    MovedMoverSeriesCannotLackFirstReading NoFirstMover := by
  sorry
end TruthCore.Results.Aristotle.Physics.MovedMoverSeriesHasFirst
