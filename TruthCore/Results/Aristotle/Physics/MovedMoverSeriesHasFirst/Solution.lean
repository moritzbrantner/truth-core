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
  intro hNoFirst
  have hInfiniteChain := hChain hNoFirst
  have hOneUnity := hUnity hInfiniteChain
  exact hImpossible (hTraversal ⟨hInfiniteChain, hOneUnity⟩)
end TruthCore.Results.Aristotle.Physics.MovedMoverSeriesHasFirst
