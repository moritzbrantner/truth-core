import TruthCore.Modal.S5Research
import TruthCore.Results.Modal.S5.Laws.Solution
namespace TruthCore.Results.Modal.S5.Projection
open TruthCore.Modal TruthCore.Modal.S5Research
open TruthCore.Isabelle.AFP.GoedelGod (MProp)
open TruthCore.Modern.Hume.Conceivability (Conception)
theorem excluded {W : Type} (F : Frame W) (C : Conception W) (P : MProp W) (w : W)
    (hFrame : ScenarioFrame F) (hBridge : ScenarioBridge F C w)
    (hContingency : ScenarioContingency F P w) : CollapseConceptionExcluded F C w := by
  intro hConceived
  have hPossible := hBridge (TruthCore.Modal.ResearchFixture.MC F
    TruthCore.Modal.ResearchFixture.allPredicates) hConceived
  have hActual := Laws.actual F w hFrame hPossible
  exact TruthCore.Results.Modal.K.Laws.no_contingency F w P hActual hContingency
end TruthCore.Results.Modal.S5.Projection
