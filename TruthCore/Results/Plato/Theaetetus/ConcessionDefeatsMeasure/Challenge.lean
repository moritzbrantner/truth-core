import TruthCore.Greek.Plato.Theaetetus
namespace TruthCore.Results.Plato.Theaetetus.ConcessionDefeatsMeasure
open TruthCore.Logic.SelfApplication
open TruthCore.Greek.Plato.Theaetetus
/-- What the restricted doctrine concedes (*Theaetetus* 171e-172a) defeats the
unrestricted measure doctrine: the concession denies the doctrine outside the
demarcated domain, and the unrestricted doctrine would give it there, as the
restriction of a norm on (agent, content) pairs to that part of its scope. No
particular case of seeming without truth-for is assumed. -/
theorem concessionDefeatsMeasure {Agent Content : Type} (Seems : Agent → Content → Prop)
    (T : TruthSemantics Agent Content) (D : Norm.Demarcation Content)
    (hConcession : RestrictedMeasureConcession Seems T D) : NotMeasureDoctrine Seems T := by
  sorry
end TruthCore.Results.Plato.Theaetetus.ConcessionDefeatsMeasure
