import TruthCore.Science.PredicateRecoding
namespace TruthCore.Results.Science.PredicateRecoding
open TruthCore.Science.PredicateRecoding
/-- Exact bounded recoding and factorization controls; no inductive norm. -/
theorem controls : Controls := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro phase feature
    cases phase <;> cases feature <;> rfl
  · intro p phase feature
    cases phase <;> cases feature <;> rfl
  · intro p
    constructor
    · intro h
      refine ⟨p false, ?_⟩
      intro phase feature
      cases phase with
      | false => rfl
      | true => exact (h feature).symm
    · rintro ⟨q, h⟩ feature
      exact (h false feature).trans (h true feature).symm
  · intro feature
    rfl
  · intro h
    have bad := h false
    contradiction
end TruthCore.Results.Science.PredicateRecoding
