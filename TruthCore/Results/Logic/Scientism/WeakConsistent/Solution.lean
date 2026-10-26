import TruthCore.Logic.Scientism
namespace TruthCore.Results.Logic.Scientism.WeakConsistent
open TruthCore.Logic.SelfApplication
open TruthCore.Logic.Scientism
/-- Weak scientism survives: claims are Booleans, every claim is in scope and
established, only `false` is empirically established and only `false` is in
the domain. The restricted norm holds, the weak thesis `true` lies outside its
domain and is established non-empirically, and the domain claim is
established empirically. Consistency, not a defense. -/
theorem weakScientismConsistent : WeakScientismConsistent := by
  refine ⟨⟨fun _ => True, fun c => c = false⟩, fun _ => True, ⟨fun c => c = false⟩, true,
    trivial, ?_, ?_, trivial, ?_, ⟨false, rfl, trivial, rfl⟩⟩
  · intro h
    cases h
  · intro h
    cases h
  · intro c hScope _
    exact hScope.2
end TruthCore.Results.Logic.Scientism.WeakConsistent
