module

public import TruthCore.Alternatives.ReligiousLanguageSemantics

@[expose] public section
namespace TruthCore.Results.Alternatives.ReligiousLanguageSemantics
open TruthCore.Alternatives.ReligiousLanguageSemantics

theorem religiousSemanticCoverage (P : Profile) (hEM : TruthCore.Logic.ExcludedMiddle) : ReligiousSemanticCases P := by
  cases hEM (LocalFaceValue P) with
  | inr h => exact Or.inr (Or.inr h)
  | inl hl =>
    cases hEM (MatchedReligiousTruthDifference P) with
    | inl hd => exact Or.inr (Or.inl ⟨hl, hd⟩)
    | inr hd =>
      apply Or.inl
      refine ⟨hl, ?_⟩
      intro s hr hc0 hc1
      constructor
      · intro ht0
        cases hEM (P.TrueIn true s) with
        | inl ht1 => exact ht1
        | inr ht1 => exact False.elim (hd ⟨s, hr, hc0, hc1, Or.inl ⟨ht0, ht1⟩⟩)
      · intro ht1
        cases hEM (P.TrueIn false s) with
        | inl ht0 => exact ht0
        | inr ht0 => exact False.elim (hd ⟨s, hr, hc0, hc1, Or.inr ⟨ht1, ht0⟩⟩)

end TruthCore.Results.Alternatives.ReligiousLanguageSemantics
