import TruthCore.Explanation.WeakAccountNecessaryBeing

namespace TruthCore.Results.Explanation.WeakAccountNecessaryBeing
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.Explanation.FixedConstituentNecessaryBeing
open TruthCore.Explanation.WeakAccountNecessaryBeing
open TruthCore.Explanation.StoppingPoints (NecessaryFact)
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic (ExcludedMiddle)

/-- The four-field account and constituent policies suffice without assuming
target contingency. The resulting ordinary bearer need not bear the target. -/
theorem necessaryBeing {W B F : Type} (A : Arena W B F) (w : W)
    (S : F → Prop) (x : F) (K : F → Set B)
    (hEM : ExcludedMiddle) (hAccount : WeakReasonClosed A w S x)
    (hFounded : Founded A w S)
    (hNonempty : AccountConstituentsNonempty S K)
    (hRealized : AccountConstituentsRealized A S K) : NecessaryBeing A.ontic w := by
  sorry

end TruthCore.Results.Explanation.WeakAccountNecessaryBeing
