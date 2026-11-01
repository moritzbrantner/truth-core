import TruthCore.Explanation.AccessibleAccountNecessaryBeing

namespace TruthCore.Results.Explanation.AccessibleAccountNecessaryBeing
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.Explanation.FixedConstituentNecessaryBeing
open TruthCore.Explanation.WeakAccountNecessaryBeing
open TruthCore.Explanation.AccessibleAccountNecessaryBeing
open TruthCore.Explanation.StoppingPoints (NecessaryFact)
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic (ExcludedMiddle)

/-- Local contingent-reason accessibility suffices for an actual ordinary
necessary bearer. No global account foundedness or target contingency is assumed. -/
theorem necessaryBeing {W B F : Type} (A : Arena W B F) (w : W)
    (S : F → Prop) (x : F) (K : F → Set B)
    (hEM : ExcludedMiddle) (hAccount : WeakReasonClosed A w S x)
    (hAccessible : SelectedAccountAccessible A w S x)
    (hNonempty : AccountConstituentsNonempty S K)
    (hRealized : AccountConstituentsRealized A S K) : NecessaryBeing A.ontic w := by
  sorry

end TruthCore.Results.Explanation.AccessibleAccountNecessaryBeing
