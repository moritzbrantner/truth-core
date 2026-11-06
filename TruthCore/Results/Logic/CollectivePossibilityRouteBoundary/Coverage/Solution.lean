module

public import TruthCore.Logic.CollectivePossibilityRouteBoundary

@[expose] public section
namespace TruthCore.Results.Logic.CollectivePossibilityRouteBoundary.Coverage
open TruthCore.Logic
open TruthCore.Logic.CollectivePossibilityRouteBoundary
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Frozen scope obligation; no historical interpretation or premise truth asserted. -/
theorem coverage (hEM : ExcludedMiddle) : CollectiveFork := by
  intro f
  cases hEM (AllIndividuallyPossible f) with
  | inr hn => exact Or.inl (fun h => False.elim (hn h))
  | inl ha =>
    cases hEM (f.Possible (fun t => ∀ x, ¬ f.IsAt x t)) with
    | inl hq => exact Or.inl (fun _ => hq)
    | inr hq => exact Or.inr ⟨ha, hq⟩

end TruthCore.Results.Logic.CollectivePossibilityRouteBoundary.Coverage
