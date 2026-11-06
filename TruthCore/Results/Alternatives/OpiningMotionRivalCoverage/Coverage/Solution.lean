module

public import TruthCore.Alternatives.OpiningMotionRivalCoverage

@[expose] public section
namespace TruthCore.Results.Alternatives.OpiningMotionRivalCoverage.Coverage
open TruthCore.Alternatives.OpiningMotionRivalCoverage
open TruthCore.Alternatives.ActPotencyRegress

/-- Analyst matching-scope rival consequence; original motion/retorsion results stay fixed. -/
theorem coverage {B R : Type} (MovedIn : B → R → Prop) (Opines : B → Prop → Prop) (asOpinion : Prop → R)
    (hEM : TruthCore.Logic.ExcludedMiddle) : OpinionMotionFork MovedIn Opines asOpinion := by
  cases hEM (Countertuple MovedIn Opines asOpinion) with
  | inl h => exact Or.inr h
  | inr hn =>
    left
    intro x p hOpines
    cases hEM (MovedIn x (asOpinion p)) with
    | inl h => exact h
    | inr h => exact False.elim (hn ⟨x, p, hOpines, h⟩)

end TruthCore.Results.Alternatives.OpiningMotionRivalCoverage.Coverage
