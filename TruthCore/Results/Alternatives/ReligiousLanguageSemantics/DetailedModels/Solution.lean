module

public import TruthCore.Alternatives.ReligiousLanguageSemantics
public import TruthCore.Results.Alternatives.ReligiousLanguageSemantics.Rejection.Solution
public import TruthCore.Results.Alternatives.ReligiousLanguageSemantics.Description.Solution

@[expose] public section
namespace TruthCore.Results.Alternatives.ReligiousLanguageSemantics
open TruthCore.Alternatives.ReligiousLanguageSemantics

theorem detailedReligiousSemanticModels : DetailedReligiousSemanticModels := by
  have hc (belief descriptive : Prop) (varied : Bool) :
      AssignedTruthTracksFact (detailedModel belief descriptive varied) := by
    intro context s content hContent
    subst content
    exact Iff.rfl
  have hu (belief descriptive : Prop) :
      MatchedTruthUniform (detailedModel belief descriptive true) := by
    intro s hr _ _
    subst s
    exact ⟨fun _ => Or.inr Bool.false_ne_true, fun _ => Or.inl rfl⟩
  have he (belief descriptive : Prop) (varied : Bool) :
      MatchedReligiousSentenceExists (detailedModel belief descriptive varied) :=
    ⟨false, rfl, rfl, rfl⟩
  have hl (varied : Bool) : LocalFaceValue (detailedModel True True varied) := by
    intro _ _
    exact ⟨rfl, ⟨trivial, rfl⟩, ⟨trivial, rfl⟩, Iff.rfl⟩
  have hd : MatchedReligiousTruthDifference (detailedModel True True false) := by
    refine ⟨false, rfl, rfl, rfl, Or.inl ⟨Or.inl rfl, ?_⟩⟩
    intro h
    cases h with
    | inl h => exact Bool.false_ne_true h.symm
    | inr h => exact h rfl
  refine ⟨⟨detailedModel True True false, hc _ _ _, hl false, hd,
    matchedDifferenceRejectsCrossDiscourse _ hd⟩, ?_, ?_, ?_⟩
  · refine ⟨detailedModel True True true, hc _ _ _, ⟨hl true, hu _ _⟩,
      he _ _ _, ⟨true, ?_, Or.inl ⟨Or.inl rfl, ?_⟩⟩, ?_⟩
    · intro h; exact Bool.false_ne_true h.symm
    · intro h
      cases h with
      | inl h => exact Bool.false_ne_true h.symm
      | inr h => exact h rfl
    · intro h; exact matchedDifferenceRejectsUniform _ h (hu _ _)
  · refine ⟨detailedModel False True true, hc _ _ _, hu _ _, he _ _ _,
      ?_, ⟨false, rfl, ?_⟩, ?_⟩
    · intro _ _; exact ⟨rfl, ⟨trivial, rfl⟩, Iff.rfl⟩
    · intro h; exact h.1
    · intro h; exact (h false rfl).2.1.1
  · have hn : NonDescriptiveReligiousWitness (detailedModel True False true) :=
      ⟨false, rfl, fun h => h.1⟩
    refine ⟨detailedModel True False true, hc _ _ _, hu _ _, he _ _ _,
      ?_, hn, nonDescriptionRejectsLocal _ hn⟩
    intro _ _; exact ⟨rfl, ⟨trivial, rfl⟩, Iff.rfl⟩

end TruthCore.Results.Alternatives.ReligiousLanguageSemantics
