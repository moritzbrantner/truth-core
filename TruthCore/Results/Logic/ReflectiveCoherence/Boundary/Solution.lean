import TruthCore.Logic.ReflectiveCoherence

namespace TruthCore.Results.Logic.ReflectiveCoherence.Boundary

open TruthCore.Logic.ReflectiveCoherence

/-- The four semantic distinctions follow constructively from shared models
and the explicitly supplied truth condition for negation. -/
theorem coherenceBoundary : CoherenceBoundary := by
  intro World Claim S
  constructor
  · intro Γ duty hEntails hCompatible
    obtain ⟨w, hModels, hDuty⟩ := hCompatible
    exact ((S.neg_true_iff w duty).mp (hEntails w hModels)) hDuty
  constructor
  · intro Γ duty hAccepts hEntails hConsistent
    obtain ⟨w, hModels⟩ := hConsistent
    exact ((S.neg_true_iff w duty).mp (hEntails w hModels)) (hModels duty hAccepts)
  constructor
  · intro Γ actual duty hTrue hEntails hModels
    exact ((S.neg_true_iff actual duty).mp (hEntails actual hModels)) hTrue
  · intro Γ p q hCompatible hFollows
    obtain ⟨w, hModels, hp⟩ := hCompatible
    exact ⟨w, hModels, hFollows w hp⟩

end TruthCore.Results.Logic.ReflectiveCoherence.Boundary
