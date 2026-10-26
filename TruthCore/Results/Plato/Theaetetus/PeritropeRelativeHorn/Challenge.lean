import TruthCore.Greek.Plato.Theaetetus
namespace TruthCore.Results.Plato.Theaetetus.PeritropeRelativeHorn
open TruthCore.Logic.SelfApplication
open TruthCore.Greek.Plato.Theaetetus
/-- Horn 2 of the peritropē (*Theaetetus* 170a-171b, every qualifier kept): by
the measure doctrine the thesis is true for Protagoras and the denial is true
for the denier; by the per-agent negation bridge the thesis is not true for
the denier. No contradiction, and nothing the holder's relative truth gives
the denier. -/
theorem peritropeRelativeHorn {Agent Content : Type} (Seems : Agent → Content → Prop)
    (T : TruthSemantics Agent Content) (neg : Content → Content) (thesis : Content) (a : Agent)
    (hMeasure : MeasureDoctrine Seems T)
    (hNeg : RelativeNegationRespected T neg)
    (hHolds : HoldsMeasureThesis Seems thesis a)
    (hDeny : SomeoneDeniesThesis Seems neg thesis) :
    RelativeHornOutcome T neg thesis a := by
  sorry
end TruthCore.Results.Plato.Theaetetus.PeritropeRelativeHorn
