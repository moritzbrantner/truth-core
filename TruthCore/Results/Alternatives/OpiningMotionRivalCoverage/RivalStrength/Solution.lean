module

public import TruthCore.Alternatives.OpiningMotionRivalCoverage

@[expose] public section
namespace TruthCore.Results.Alternatives.OpiningMotionRivalCoverage.RivalStrength
open TruthCore.Alternatives.OpiningMotionRivalCoverage
open TruthCore.Alternatives.ActPotencyRegress

/-- Analyst matching-scope rival consequence; original motion/retorsion results stay fixed. -/
theorem rivalStrength {B R : Type} (MovedIn : B → R → Prop) (Opines : B → Prop → Prop) (asOpinion : Prop → R)
    (h : ChangeUnrealButAppearsReading MovedIn Opines) : Countertuple MovedIn Opines asOpinion := by
  obtain ⟨hNone, x, p, hOpines⟩ := h
  exact ⟨x, p, hOpines, hNone x (asOpinion p)⟩

end TruthCore.Results.Alternatives.OpiningMotionRivalCoverage.RivalStrength
