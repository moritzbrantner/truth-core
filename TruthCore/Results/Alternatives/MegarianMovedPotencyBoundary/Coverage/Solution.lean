module

public import TruthCore.Alternatives.MegarianMovedPotencyBoundary

@[expose] public section
namespace TruthCore.Results.Alternatives.MegarianMovedPotencyBoundary.Coverage
open TruthCore.Alternatives.MegarianMovedPotencyBoundary
open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics
open TruthCore.Models.MegarianCapacity

/-- Analyst obligation; source meanings and old frozen results are preserved. -/
theorem coverage {B R : Type} (MovedIn InPotency : B → R → Prop)
    (hEM : TruthCore.Logic.ExcludedMiddle) : MovedPotencyFork MovedIn InPotency := by
  cases hEM (Countertuple MovedIn InPotency) with
  | inl h => exact Or.inr h
  | inr hn =>
    left
    intro x r hm
    cases hEM (InPotency x r) with
    | inl h => exact h
    | inr h => exact False.elim (hn ⟨x, r, hm, h⟩)

end TruthCore.Results.Alternatives.MegarianMovedPotencyBoundary.Coverage
