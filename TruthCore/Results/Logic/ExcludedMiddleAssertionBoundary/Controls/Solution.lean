module

public import TruthCore.Logic.ExcludedMiddleAssertionBoundary
public import TruthCore.Results.Logic.ExcludedMiddleIrrefutable.Solution

@[expose] public section
namespace TruthCore.Results.Logic.ExcludedMiddleAssertionBoundary.Controls
open TruthCore.Logic
open TruthCore.Logic.ExcludedMiddleAssertionBoundary
theorem controls (hEM : ExcludedMiddle) : Controls := by
  constructor
  · refine ⟨(fun _ _ => False), (fun _ _ => False), ?_, hEM, ?_⟩
    · refine ⟨?_, ⟨(), True, ?_⟩,
        TruthCore.Results.Logic.ExcludedMiddleIrrefutable.excludedMiddleIrrefutable⟩
      · intro stage p h
        exact False.elim h
      · intro h
        exact h
    · intro h
      exact h () True
  · refine ⟨(fun _ _ => False), (fun stage _ => stage = false), ?_, ?_⟩
    · intro h
      have impossible := h.1 false True rfl
      cases impossible with
      | inl hFalse => exact hFalse
      | inr hFalse => exact hFalse
    · intro h
      exact Bool.noConfusion (h true True)
end TruthCore.Results.Logic.ExcludedMiddleAssertionBoundary.Controls
