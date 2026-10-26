import TruthCore.Greek.Plato.Theaetetus
import TruthCore.Results.Logic.TruthPilot.ConflictingOpinionsTest.Solution
namespace TruthCore.Results.Plato.Theaetetus.PeritropeAbsoluteHorn
open TruthCore.Logic.SelfApplication
open TruthCore.Logic.TruthPilot
open TruthCore.Greek.Plato.Theaetetus
/-- Horn 1 of the peritropē (*Theaetetus* 171a-c, unqualified reading): if
Protagoras asserts his thesis and sincerely (so it seems so to him), someone opines its denial, the doctrine's scope
covers both, and unindexed truth respects negation, then not every opinion in
scope is true. Composes the pilot's conflicting-opinions test with the
conflict located in the thesis itself. -/
theorem peritropeAbsoluteHorn {Agent Content : Type} (Asserts Seems : Agent → Content → Prop)
    (T : TruthSemantics Agent Content) (neg : Content → Content) (scope : Content → Prop)
    (thesis : Content) (a : Agent)
    (hAsserts : AssertsMeasureThesis Asserts thesis a)
    (hSincere : SincereAsserter Asserts Seems a)
    (hDeny : SomeoneDeniesThesis Seems neg thesis)
    (hNeg : NegationRespected T.trueAbs neg)
    (hScope : PeritropeScope scope neg thesis) :
    NotUnqualifiedAllOpinionsTrue scope Seems T := by
  sorry
end TruthCore.Results.Plato.Theaetetus.PeritropeAbsoluteHorn
