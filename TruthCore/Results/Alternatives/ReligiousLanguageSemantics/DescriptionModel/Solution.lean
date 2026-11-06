module

public import TruthCore.Alternatives.ReligiousLanguageSemantics
public import TruthCore.Results.Alternatives.ReligiousLanguageSemantics.Description.Solution

@[expose] public section
namespace TruthCore.Results.Alternatives.ReligiousLanguageSemantics
open TruthCore.Alternatives.ReligiousLanguageSemantics

theorem nonDescriptiveModel : NonDescriptiveReligiousModel := by
  let P : Profile := { model True true with FactRepresentation := fun _ _ _ => False }
  have hn : NonDescriptiveReligiousWitness P := ⟨false, rfl, fun h => h⟩
  refine ⟨P, hn, ?_, nonDescriptionRejectsLocal P hn⟩
  intro s hr _ _
  subst s
  exact ⟨fun _ => Or.inr Bool.false_ne_true, fun _ => Or.inl rfl⟩

end TruthCore.Results.Alternatives.ReligiousLanguageSemantics
