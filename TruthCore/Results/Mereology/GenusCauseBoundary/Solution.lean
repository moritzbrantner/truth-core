import TruthCore.Mereology.GenusCauseBoundary
import TruthCore.Results.Aquinas.SummaTheologiae.EssenceEsseExternalCause.Solution
import TruthCore.Results.Aristotle.Metaphysics.BeingNotAGenus.Solution

namespace TruthCore.Results.Mereology.GenusCauseBoundary
open TruthCore.Mereology.GenusCauseBoundary
open TruthCore.Greek.Aristotle.Metaphysics
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

private theorem taxonomy : Taxonomy := by
  have hHas : EveryGenusHasADifferentiaReading isGenus differentiaOf := by
    intro g hg
    subst g
    exact ⟨.differentia, rfl, rfl⟩
  have hBeing : DifferentiaeAreBeingsReading isGenus differentiaOf saidOf .being := by
    intro _ _ _ _
    exact Or.inl rfl
  have hNot : GenusNotSaidOfOwnDifferentiaeReading isGenus differentiaOf saidOf := by
    intro g d hg hd hs
    rcases hs with he | ⟨he, hd'⟩ | ⟨he, hd'⟩
    · exact Term.noConfusion (hg.symm.trans he)
    · exact Term.noConfusion (hd.1.symm.trans hd')
    · exact Term.noConfusion (hg.symm.trans he)
  refine ⟨hHas, hBeing, hNot, ?_, ?_, ?_⟩
  · exact fun _ _ h => h
  · intro _
    exact ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl⟩),
      Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  · exact TruthCore.Results.Aristotle.Metaphysics.BeingNotAGenus.beingNotAGenus
      isGenus differentiaOf saidOf .being hHas hBeing hNot

/-- Reuses the checked q.3 a.4 positive model, then changes only the causal
field for the first comparison. A separate identity copy tests the absent
genus-to-real-distinction mapping. The source's further metaphysical premises
are not silently inserted into these finite interpretations. -/
theorem checks : Boundary := by
  obtain ⟨p, hc, hd, he, hEx, hNo, _hRequires⟩ :=
    TruthCore.Results.Aquinas.SummaTheologiae.EssenceEsseExternalCause.premiseOmissionsAndControl.2.2
  let p₀ : Profile Bool Bool Unit := { p with CausesIn := fun _ _ _ => False }
  let pᵢ : Profile Bool Bool Unit :=
    { p with CausesIn := fun _ _ _ => False, esseOf := p.essenceOf }
  have hn₀ : ∀ x, ¬HasExternalEsseCause p₀ x := by
    intro _ ⟨_, _, _, h⟩
    exact h
  have hnᵢ : ∀ x, ¬HasExternalEsseCause pᵢ x := by
    intro _ ⟨_, _, _, h⟩
    exact h
  have hNo₀ : EssentialPrinciplesCannotCauseDistinctEsseReading p₀ := hNo
  have hd₀ : DistinctEsseAt p₀ false := hd
  have hNotEx : ¬DistinctEsseCauseDichotomyReading p₀ := by
    intro h
    exact hn₀ false
      (TruthCore.Results.Aquinas.SummaTheologiae.EssenceEsseExternalCause.distinctEsseExternalFromExhaustion p₀ h hNo₀ false hd₀)
  refine ⟨taxonomy, p₀, p, pᵢ, ?_, ?_, hc, ?_, hd₀, hd, hNo₀, hNo,
    ?_, hn₀ false, he, hNotEx, hEx, rfl, rfl, ?_, ?_, hnᵢ, ?_, ?_, hd.1⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact fun _ _ h => h.elim
  · exact fun _ _ h => h.elim
  · exact fun _ _ _ h => h
  · exact fun _ => rfl
  · exact fun _ _ _ h => h
  · intro x hx
    exact False.elim (hx.2 rfl)
  · intro x hx
    exact False.elim (hx.2 rfl)

end TruthCore.Results.Mereology.GenusCauseBoundary
