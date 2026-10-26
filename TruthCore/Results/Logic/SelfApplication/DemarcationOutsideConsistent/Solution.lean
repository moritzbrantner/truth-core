import TruthCore.Logic.SelfApplication
namespace TruthCore.Results.Logic.SelfApplication.DemarcationOutsideConsistent
open TruthCore.Logic.SelfApplication
/-- A weak thesis outside its own domain is consistent. Claims are Booleans;
the domain and the standard are both `{false}`, only `true` is acceptable,
and the weak thesis is `true`: in the strong scope, acceptable, outside the
domain and failing the standard, while the restricted norm holds. -/
theorem demarcationOutsideConsistent : DemarcationOutsideConsistent := by
  refine ⟨⟨fun _ => True, fun c => c = false⟩, ⟨fun c => c = false⟩, fun c => c = true, true,
    trivial, ?_, ?_, rfl, ?_⟩
  · intro h
    cases h
  · intro h
    cases h
  · intro c hScope _
    exact hScope.2
end TruthCore.Results.Logic.SelfApplication.DemarcationOutsideConsistent
