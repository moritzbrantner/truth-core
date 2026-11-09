module

public import TruthCore.Metaethics.InternalCounterfactual

@[expose] public section
namespace TruthCore.Results.Metaethics.InternalCounterfactual
open TruthCore.Metaethics.InternalCounterfactual

/-- Finite separation of internal acceptance and the supplied truth test. -/
theorem controls : Controls := by
  constructor
  · refine ⟨⟨True.intro, rfl⟩, ?_, True.intro, rfl, ?_, ?_⟩
    · intro h
      exact h.2 true rfl
    · intro h
      exact h
    · intro h
      cases h
  · refine ⟨⟨True.intro, ?_⟩, ?_, rfl, ?_⟩
    · intro p _
      cases p <;> exact True.intro
    · intro h
      exact h.1
    · intro h
      cases h

end TruthCore.Results.Metaethics.InternalCounterfactual
