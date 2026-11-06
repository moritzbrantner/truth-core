module

public import TruthCore.Alternatives.ReligiousLanguageSemantics
public import TruthCore.Results.Alternatives.ReligiousLanguageSemantics.Rejection.Solution

@[expose] public section
namespace TruthCore.Results.Alternatives.ReligiousLanguageSemantics
open TruthCore.Alternatives.ReligiousLanguageSemantics

theorem religiousSemanticModels : ReligiousSemanticModels := by
  have hl : LocalFaceValue (model True false) := by
    intro s hr
    subst s
    exact ⟨trivial, trivial, trivial, Iff.rfl⟩
  have hd : MatchedReligiousTruthDifference (model True false) := by
    refine ⟨false, rfl, trivial, trivial, Or.inl ⟨Or.inl rfl, ?_⟩⟩
    intro h
    cases h with
    | inl h => exact Bool.false_ne_true h.symm
    | inr h => exact h rfl
  have hu : MatchedTruthUniform (model True true) := by
    intro s hr _ _
    subst s
    exact ⟨fun _ => Or.inr Bool.false_ne_true, fun _ => Or.inl rfl⟩
  refine ⟨⟨model True false, hl, hd,
    matchedDifferenceRejectsCrossDiscourse _ hd⟩, ?_, ?_⟩
  · refine ⟨model True true, ⟨?_, hu⟩,
      ⟨true, Or.inl ⟨Or.inl rfl, ?_⟩⟩, ?_⟩
    · intro s hr; subst s; exact ⟨trivial, trivial, trivial, Iff.rfl⟩
    · intro h
      cases h with
      | inl h => exact Bool.false_ne_true h.symm
      | inr h => exact h rfl
    · intro h; exact matchedDifferenceRejectsUniform _ h hu
  · refine ⟨model False true, ?_, ?_⟩
    · intro s hr _ _
      subst s
      exact ⟨fun _ => Or.inr Bool.false_ne_true, fun _ => Or.inl rfl⟩
    · intro h; exact (h false rfl).2.1

end TruthCore.Results.Alternatives.ReligiousLanguageSemantics
