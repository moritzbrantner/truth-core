import TruthCore.Results.Comparison.NaturalisticRealism.Model
namespace TruthCore.Results.Comparison.NaturalisticRealism.UnrecognizedIdentityPossible
open TruthCore.Metaethics.NaturalisticRealism
open TruthCore.Comparison.NaturalisticRealism

theorem unrecognizedIdentityPossible : UnrecognizedIdentityPossible := by
  refine ⟨Bool, Bool, false, true, (fun _ a => a = true),
    (fun _ _ => False), Bool.noConfusion, rfl, id, ?_, ?_⟩
  · exact ⟨true, rfl⟩
  · exact ⟨false, Bool.noConfusion⟩

end TruthCore.Results.Comparison.NaturalisticRealism.UnrecognizedIdentityPossible
