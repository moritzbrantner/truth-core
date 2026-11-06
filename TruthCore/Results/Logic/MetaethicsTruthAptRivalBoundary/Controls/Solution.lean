module

public import TruthCore.Logic.MetaethicsTruthAptRivalBoundary
public import TruthCore.Results.Comparison.QuasiRealism.DeviatesOnRobustTruth.Solution

@[expose] public section
namespace TruthCore.Results.Logic.MetaethicsTruthAptRivalBoundary.Controls
open TruthCore.English.VanRoojen
open TruthCore.Logic.MetaethicsTruthAptRivalBoundary
theorem controls : Controls := by
  constructor
  · obtain ⟨Moral, Minimal, Robust, hQuasi, hNoMoral, _⟩ :=
      TruthCore.Results.Comparison.QuasiRealism.DeviatesOnRobustTruth.withoutMoralSentenceMatch
    refine ⟨Moral, Minimal, Robust, hQuasi, ?_, ?_⟩
    · intro s hs
      cases s
      exact False.elim (hNoMoral hs)
    · intro s hs
      cases s
      exact hNoMoral hs
  · obtain ⟨Moral, Minimal, Robust, hNoQuasi, hMoral, hNoDeviation⟩ :=
      TruthCore.Results.Comparison.QuasiRealism.DeviatesOnRobustTruth.withoutQuasiRealismMatch
    refine ⟨Moral, Minimal, Robust, hMoral, hNoQuasi, ?_⟩
    intro hRobust
    apply hNoDeviation
    intro hEquivalent
    exact hNoQuasi (hEquivalent.mpr hRobust)
end TruthCore.Results.Logic.MetaethicsTruthAptRivalBoundary.Controls
