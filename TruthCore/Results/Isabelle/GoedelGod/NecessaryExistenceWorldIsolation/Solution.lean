import TruthCore.Isabelle.AFP.GoedelGod

namespace TruthCore.Results.Isabelle.GoedelGod.NecessaryExistenceWorldIsolation

open TruthCore.Isabelle.AFP.GoedelGod

/-- The singleton-in-world property is a perfectly admissible intensional
property in the AFP embedding. Its being an essence makes distinct accessible
worlds incompatible with the `NE` definition. No excluded middle, positivity,
reflexivity, or symmetry is used. -/
theorem checks {World Ind : Type} : NecessaryExistenceWorldIsolation World Ind := by
  intro F x w
  constructor
  · intro hNE next hAccess
    let Φ : Property World Ind := fun y v => y = x ∧ v = w
    have hEss : Essence F Φ x w := by
      constructor
      · exact ⟨rfl, rfl⟩
      · intro Ψ hΨ v _ y hΦ
        obtain ⟨rfl, rfl⟩ := hΦ
        exact hΨ
    obtain ⟨y, hy⟩ := hNE Φ hEss next hAccess
    exact hy.2
  · intro hIsolated Φ hEss next hAccess
    have hSame : next = w := hIsolated next hAccess
    cases hSame
    exact ⟨x, hEss.1⟩

end TruthCore.Results.Isabelle.GoedelGod.NecessaryExistenceWorldIsolation
