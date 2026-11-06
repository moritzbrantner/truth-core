module

public import TruthCore.Metaethics.GoodnessFormEnd

@[expose] public section
namespace TruthCore.Results.Metaethics.GoodnessFormEndFork
open TruthCore.Logic
open TruthCore.Metaethics.GoodnessFormEnd

/-- The decision principle is a hypothesis; no preferred cell is selected. -/
theorem failureElimination (hEM : ExcludedMiddle) : FailureElimination := by
  intro f hNoSurplus hNoOmission x p
  constructor
  · intro hGood
    cases hEM (DueActuality f x p) with
    | inl h => exact h
    | inr h => exact False.elim (hNoSurplus ⟨x, p, hGood, h⟩)
  · intro hDue
    cases hEM (f.GoodIn x p) with
    | inl h => exact h
    | inr h => exact False.elim (hNoOmission ⟨x, p, hDue, h⟩)

/-- Surplus and omission can overlap; their absence yields exact coextension. -/
theorem definitionFork (hEM : ExcludedMiddle) : DefinitionFork := by
  intro f
  cases hEM (SurplusGood f) with
  | inl h => exact Or.inr (Or.inl h)
  | inr hNoSurplus =>
    cases hEM (OmittedDueGood f) with
    | inl h => exact Or.inr (Or.inr h)
    | inr hNoOmission => exact Or.inl (failureElimination hEM f hNoSurplus hNoOmission)

end TruthCore.Results.Metaethics.GoodnessFormEndFork
