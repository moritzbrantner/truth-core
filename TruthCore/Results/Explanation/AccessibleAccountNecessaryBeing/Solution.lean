import TruthCore.Explanation.AccessibleAccountNecessaryBeing
import TruthCore.Results.Explanation.FixedConstituentNecessaryBeing.Solution

namespace TruthCore.Results.Explanation.AccessibleAccountNecessaryBeing
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.Explanation.FixedConstituentNecessaryBeing
open TruthCore.Explanation.WeakAccountNecessaryBeing
open TruthCore.Explanation.AccessibleAccountNecessaryBeing
open TruthCore.Explanation.StoppingPoints (NecessaryFact)
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic (ExcludedMiddle)

/-- The old global Founded input implies accessibility at every selected fact.
No converse or strictness is asserted by this projection. -/
theorem accessibleOfFounded {W B F : Type} {A : Arena W B F} {w : W}
    {S : F → Prop} (x : F) (h : Founded A w S) :
    SelectedAccountAccessible A w S x := h.apply x

/-- Local contingent-reason accessibility suffices for an actual ordinary
necessary bearer. No global account foundedness or target contingency is assumed. -/
theorem necessaryBeing {W B F : Type} (A : Arena W B F) (w : W)
    (S : F → Prop) (x : F) (K : F → Set B)
    (hEM : ExcludedMiddle) (hAccount : WeakReasonClosed A w S x)
    (hAccessible : SelectedAccountAccessible A w S x)
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
    have impossible : ∀ f, Acc (ContingentReason A w S) f → S f → False := by
      intro f hf
      induction hf with
      | intro f _ ih =>
        intro hs
        obtain ⟨r, hr⟩ := hAccount.covered f hs (contingent f hs)
        have hsr := hAccount.closed r f hs hr
        exact ih r ⟨hsr, hs, hr, contingent r hsr, contingent f hs⟩ hsr
    exact False.elim (impossible x hAccessible hAccount.explanandum)

end TruthCore.Results.Explanation.AccessibleAccountNecessaryBeing
