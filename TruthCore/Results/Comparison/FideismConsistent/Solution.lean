module

public import TruthCore.Comparison.Fideism

@[expose] public section

namespace TruthCore.Results.Comparison.FideismConsistent
open TruthCore.Alternatives.Fideism
open TruthCore.Comparison.Fideism

/-- The fideist bundle WF-N is consistent: in a practice with one move that is
endorsed by its own standards and correct, and that answers to no standard of
shared reason, both fideist commitments hold. -/
theorem wittgensteinianFideismConsistent : WittgensteinianFideismConsistent := by
  exact ⟨⟨Unit, fun _ => True, fun _ => True, fun _ => False, fun _ => False,
    fun _ => False⟩, fun _ _ => trivial, fun _ hShared => hShared.elim⟩

end TruthCore.Results.Comparison.FideismConsistent
