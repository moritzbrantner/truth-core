import TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.BoundedOmission.Solution

/-! Registered singleton populations from #606. These evaluations describe the
stipulated interpretation, never its metaphysical admissibility. -/
namespace TruthCore.Models.BoundedOmission
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.BoundedOmission

/-- Bound supplied as a closed registry argument. -/
def pairBound : Nat := 2

/-- Exhaustive enumeration of the shared world/roster carrier. -/
theorem enumerate : ∀ x : Slot, x = Slot.a ∨ x = Slot.b ∨ x = Slot.c := by
  intro x
  cases x with
  | a => exact Or.inl rfl
  | b => exact Or.inr (Or.inl rfl)
  | c => exact Or.inr (Or.inr rfl)

/-- Every selection of at most two is jointly omissible. -/
theorem pairs : UpTo singletonFrame singletonExists Slot.a pairBound :=
  TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.BoundedOmission.checks.2.2.2.2.2.1

/-- Each candidate can be absent. -/
theorem individual : IndividualContingency singletonFrame singletonExists Slot.a :=
  TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.BoundedOmission.checks.2.2.2.2.2.2.2.1

/-- Every successor contains its own singleton. -/
theorem populated : DeDicto singletonFrame singletonExists Slot.a :=
  TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.BoundedOmission.checks.2.2.2.2.2.2.2.2.1

/-- No fixed candidate is necessary. -/
theorem noNecessary : ¬ DeRe singletonFrame singletonExists Slot.a :=
  TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.BoundedOmission.checks.2.2.2.2.2.2.2.2.2.1

/-- No accessible population is empty. -/
theorem noEmpty : ¬ JointAbsence singletonFrame singletonExists Slot.a :=
  TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.BoundedOmission.checks.2.2.2.2.2.2.2.2.2.2
end TruthCore.Models.BoundedOmission
