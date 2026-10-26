import TruthCore.Logic.SelfApplication
namespace TruthCore.Results.Logic.SelfApplication.ScopeNeeded
open TruthCore.Logic.SelfApplication
/-- Countermodel for a dropped scope premise: a norm with empty scope and an
unmeetable standard holds while an acceptable claim fails the standard. -/
theorem scopePremiseNeeded : ScopePremiseNeeded := by
  refine ⟨⟨fun _ => False, fun _ => False⟩, fun _ => True, true, ?_, ?_, ?_, trivial⟩
  · intro h
    exact h
  · intro h
    exact h
  · intro c hScope _
    exact hScope
end TruthCore.Results.Logic.SelfApplication.ScopeNeeded
