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
  -- The measure doctrine as a norm with seeming as acceptance.
  let N : Norm (Agent × Content) := ⟨fun _ => True, fun x => T.trueFor x.1 x.2⟩
  let Outside : Norm.Demarcation (Agent × Content) := ⟨fun x => ¬ D.inDomain x.2⟩
  intro hMeasure
  have hHolds : N.Holds (fun x => Seems x.1 x.2) := fun x _ hx => hMeasure x.1 x.2 hx
  have hOutside : (N.restrict Outside).Holds (fun x => Seems x.1 x.2) := Norm.holds_restrict hHolds
  exact hConcession (fun a p hOut hSeems => hOutside (a, p) ⟨trivial, hOut⟩ hSeems)
end TruthCore.Results.Plato.Theaetetus.ConcessionDefeatsMeasure
