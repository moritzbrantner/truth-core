module

public import TruthCore.Alternatives.OpiningMotionRivalCoverage

@[expose] public section
namespace TruthCore.Results.Alternatives.OpiningMotionRivalCoverage.CounterFailure
open TruthCore.Alternatives.OpiningMotionRivalCoverage
open TruthCore.Alternatives.ActPotencyRegress

/-- Analyst matching-scope rival consequence; original motion/retorsion results stay fixed. -/
theorem counterFailure {B R : Type} (MovedIn : B → R → Prop) (Opines : B → Prop → Prop) (asOpinion : Prop → R)
    (h : Countertuple MovedIn Opines asOpinion) : NormFails MovedIn Opines asOpinion := by
  obtain ⟨x, p, hOpines, hNotMoved⟩ := h
  exact fun hNorm => hNotMoved (hNorm x p hOpines)

end TruthCore.Results.Alternatives.OpiningMotionRivalCoverage.CounterFailure
