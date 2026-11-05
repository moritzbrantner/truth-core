module

public import TruthCore.Logic.ReflectiveCoherence

@[expose] public section

namespace TruthCore.Results.Logic.ReflectiveCoherence.Limits

open TruthCore.Logic.ReflectiveCoherence

/-- A consistent duty-denying worldview can be selected by a consistency-only
policy even when the duty-content is true. Separately, an empty worldview does
not explicitly endorse a content entailed by its one-world semantics. -/
theorem reflectiveCoherenceLimits : ReflectiveCoherenceLimits := by
  have hDenierModels : Models twoWorldSemantics deniesDuty false := by
    intro p hp
    change false = p
    exact hp.symm
  constructor
  · constructor
    · rfl
    constructor
    · intro Γ _ hOught
      change Γ = deniesDuty at hOught
      rw [hOught]
      exact ⟨false, hDenierModels⟩
    · intro hNorm
      have hCompatible : Compatible twoWorldSemantics deniesDuty true :=
        hNorm deniesDuty trivial rfl
      obtain ⟨w, hModels, hTrue⟩ := hCompatible
      have hFalse : w = false := hModels false rfl
      have hTrue' : w = true := hTrue
      have hAbsurd : false = true := hFalse.symm.trans hTrue'
      cases hAbsurd
  · constructor
    · exact ⟨(), by intro p hp; exact False.elim hp⟩
    constructor
    · intro w _
      change true = true
      rfl
    · intro h
      exact h

end TruthCore.Results.Logic.ReflectiveCoherence.Limits
