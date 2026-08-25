import TruthCore.Greek.Aristotle.Physics.BookIII.Chapter4

namespace TruthCore.Results.Aristotle.Physics.InfiniteNoPrinciple

open TruthCore.Greek.Aristotle.Physics

/--
If having a prior principle would limit the infinite, while the infinite under discussion is
not limited, then it has no such principle.

This verifies only the dialectical inference in III.4, not the existence of a separate or
actually infinite entity.
-/
theorem infiniteHasNoPrinciple
    (InfiniteHasPrinciple : Prop)
    (InfiniteIsLimited : Prop)
    (hWouldLimit :
      InfinitePrincipleWouldLimitReading InfiniteHasPrinciple InfiniteIsLimited)
    (hNotLimited : InfiniteNotLimitedReading InfiniteIsLimited) :
    InfiniteHasNoPrincipleReading InfiniteHasPrinciple := by
  sorry

end TruthCore.Results.Aristotle.Physics.InfiniteNoPrinciple
