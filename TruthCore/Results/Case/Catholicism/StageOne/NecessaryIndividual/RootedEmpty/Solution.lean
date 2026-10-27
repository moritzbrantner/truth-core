import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.EmptyWorldFork

namespace TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.RootedEmpty
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual

/-- A local root causes every present nonroot in the finite interpretation. -/
private theorem dependentCoverage : RootedEmptyDependentCoverage := by
  intro world effect hExists hNonroot
  refine ⟨0, ?_⟩
  exact ⟨⟨hExists.1, Or.inl rfl⟩, hExists, rfl, hNonroot⟩

/-- An effect of a root edge is nonroot, so it cannot itself be the root
cause of a second edge at the same world. -/
private theorem noTwoStepCause : RootedEmptyNoTwoStepCause := by
  intro world a b c first second
  exact first.2.2.2 second.2.2.1

/-- Constructive check of the three-world/three-individual interpretation,
including its independent one-step causal bound and accessible empty world. -/
theorem checks : RootedEmptyCountermodel := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, dependentCoverage, noTwoStepCause⟩
  · intro world
    trivial
  · trivial
  · refine ⟨0, ?_⟩
    exact ⟨(by decide), Or.inl rfl⟩
  · intro next _ hPopulated
    obtain ⟨x, hx⟩ := hPopulated
    exact ⟨hx.1, Or.inl rfl⟩
  · refine ⟨0, trivial, ?_⟩
    rintro ⟨x, hx⟩
    exact hx.1 rfl
  · intro hDeDicto
    obtain ⟨x, hx⟩ := hDeDicto 0 trivial
    exact hx.1 rfl
  · rintro ⟨x, hx⟩
    exact (hx 0 trivial).1 rfl
end TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.RootedEmpty
