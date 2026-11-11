module
public import TruthCore.Ethics.AgencyNeutrality
@[expose] public section
namespace TruthCore.Results.Ethics.AgencyNeutrality
open TruthCore.Ethics.HardCaseTyped TruthCore.Ethics.AgencyNeutrality
theorem controls : TruthCore.Ethics.AgencyNeutrality.Controls := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by decide⟩
  · exact ⟨fun _ => rfl, fun _ _ _ h => congrArg _ h, by decide⟩
  · intro R self
    exact ⟨fun h p q => h p q (self q), fun h p q _ => h p q⟩
  · exact ⟨fun _ _ => True, fun _ => True.intro,
      fun _ _ _ => True.intro, True.intro⟩
  · exact ⟨fun p q => p = q, fun _ => rfl, by decide⟩
  · exact ⟨fun _ _ => False, fun _ _ h => h, fun h => h⟩
end TruthCore.Results.Ethics.AgencyNeutrality
