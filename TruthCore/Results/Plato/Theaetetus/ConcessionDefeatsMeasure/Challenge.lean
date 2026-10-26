import TruthCore.Greek.Plato.Theaetetus
namespace TruthCore.Results.Plato.Theaetetus.ConcessionDefeatsMeasure
open TruthCore.Logic.SelfApplication
open TruthCore.Greek.Plato.Theaetetus
/-- What the restricted doctrine concedes (*Theaetetus* 171e-172a) defeats the
unrestricted measure doctrine: the measure doctrine is a norm on
(agent, content) pairs with seeming as acceptance and truth-for-the-agent as
standard, and the concession is a counterexample to it outside the domain. -/
theorem concessionDefeatsMeasure {Agent Content : Type} (Seems : Agent → Content → Prop)
    (T : TruthSemantics Agent Content) (D : Norm.Demarcation Content)
    (hConcession : RestrictedMeasureConcession Seems T D) : NotMeasureDoctrine Seems T := by
  sorry
end TruthCore.Results.Plato.Theaetetus.ConcessionDefeatsMeasure
