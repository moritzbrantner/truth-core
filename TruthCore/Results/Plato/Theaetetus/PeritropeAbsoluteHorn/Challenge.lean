import TruthCore.Greek.Plato.Theaetetus
import TruthCore.Results.Logic.TruthPilot.ConflictingOpinionsTest.Solution
namespace TruthCore.Results.Plato.Theaetetus.PeritropeAbsoluteHorn
open TruthCore.Logic.SelfApplication
open TruthCore.Logic.TruthPilot
open TruthCore.Greek.Plato.Theaetetus
/-- Horn 1 of the peritropē (*Theaetetus* 171a-c, unqualified reading): if
Protagoras holds his thesis, someone opines its denial, the doctrine's scope
covers both, and unindexed truth respects negation, then not every opinion in
scope is true. Composes the pilot's conflicting-opinions test with the
conflict located in the thesis itself. -/
theorem peritropeAbsoluteHorn {Agent Content : Type} (Seems : Agent → Content → Prop)
    (T : TruthSemantics Agent Content) (neg : Content → Content) (scope : Content → Prop)
    (thesis : Content) (a : Agent)
    (hHolds : HoldsMeasureThesis Seems thesis a)
    (hDeny : SomeoneDeniesThesis Seems neg thesis)
    (hNeg : NegationRespected T.trueAbs neg)
    (hScope : PeritropeScope scope neg thesis) :
    NotUnqualifiedAllOpinionsTrue scope Seems T := by
  sorry
end TruthCore.Results.Plato.Theaetetus.PeritropeAbsoluteHorn
