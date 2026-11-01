import TruthCore.Explanation.WeakAccountNecessaryBeing
import TruthCore.Results.Explanation.FixedConstituentNecessaryBeing.Solution
import TruthCore.Results.Explanation.ExplanatoryAdequacy.Solution

namespace TruthCore.Results.Explanation.WeakAccountNecessaryBeing
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.Explanation.FixedConstituentNecessaryBeing
open TruthCore.Explanation.WeakAccountNecessaryBeing
open TruthCore.Explanation.StoppingPoints (NecessaryFact)
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic (ExcludedMiddle)

/-- Original five-field accounts imply the weaker four-field interface. -/
theorem ofReasonClosed {W B F : Type} {A : Arena W B F} {w : W}
    {S : F → Prop} {x : F} (h : ReasonClosed A w S x) :
    WeakReasonClosed A w S x :=
  ⟨h.explanandum, h.truthful, h.closed, h.covered⟩

/-- The four-field account and constituent policies suffice without assuming
target contingency. The resulting ordinary bearer need not bear the target. -/
theorem necessaryBeing {W B F : Type} (A : Arena W B F) (w : W)
    (S : F → Prop) (x : F) (K : F → Set B)
    (hEM : ExcludedMiddle) (hAccount : WeakReasonClosed A w S x)
    (hFounded : Founded A w S)
    (hNonempty : AccountConstituentsNonempty S K)
    (hRealized : AccountConstituentsRealized A S K) : NecessaryBeing A.ontic w := by
  have realize (f : F) (hf : S f) (hn : NecessaryFact A w f) :
      NecessaryBeing A.ontic w :=
    TruthCore.Results.Explanation.FixedConstituentNecessaryBeing.necessaryBeingOfFact
      A w f K (hAccount.truthful f hf) hn (hNonempty f hf) (hRealized f hf)
  cases hEM (NecessaryBeing A.ontic w) with
  | inl h => exact h
  | inr hNo =>
    have contingent (f : F) (hf : S f) : Contingent A w f := by
      refine ⟨hAccount.truthful f hf, ?_⟩
      cases hEM (∃ v, Access A w v ∧ ¬ A.holds v f) with
      | inl h => exact h
      | inr hNoFailure =>
        have hn : NecessaryFact A w f := by
          intro v hv
          cases hEM (A.holds v f) with
          | inl h => exact h
          | inr h => exact False.elim (hNoFailure ⟨v, hv, h⟩)
        exact False.elim (hNo (realize f hf hn))
    exact False.elim
      (TruthCore.Results.Explanation.ExplanatoryAdequacy.forced
        hAccount.explanandum (contingent x hAccount.explanandum) hFounded
        (fun c hc _ hNoContingentReason => by
          obtain ⟨r, hr⟩ := hAccount.covered c hc (contingent c hc)
          have hs := hAccount.closed r c hc hr
          exact hNoContingentReason r hs hr (contingent r hs)))

end TruthCore.Results.Explanation.WeakAccountNecessaryBeing
