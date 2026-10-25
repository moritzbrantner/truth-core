import TruthCore.Modal.S5Research
namespace TruthCore.Results.Modal.S5.Projection
open TruthCore.Modal TruthCore.Modal.S5Research
open TruthCore.Isabelle.AFP.GoedelGod (MProp)
open TruthCore.Modern.Hume.Conceivability (Conception)
theorem excluded {W : Type} (F : Frame W) (C : Conception W) (P : MProp W) (w : W)
    (hFrame : ScenarioFrame F) (hBridge : ScenarioBridge F C w)
    (hContingency : ScenarioContingency F P w) : CollapseConceptionExcluded F C w := by
  sorry
end TruthCore.Results.Modal.S5.Projection
