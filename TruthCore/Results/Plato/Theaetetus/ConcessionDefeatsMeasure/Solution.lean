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
  obtain ⟨a, p, hOut, hSeems, hNotTrue⟩ := hConcession
  let N : Norm (Agent × Content) := ⟨fun _ => True, fun x => T.trueFor x.1 x.2⟩
  let D' : Norm.Demarcation (Agent × Content) := ⟨fun x => D.inDomain x.2⟩
  have hConc : N.Concedes D' (fun x => Seems x.1 x.2) (a, p) := ⟨trivial, hOut, hSeems, hNotTrue⟩
  intro hMeasure
  exact Norm.not_holds_of_counterexample (Norm.counterexample_of_concedes hConc)
    (fun x _ hx => hMeasure x.1 x.2 hx)
end TruthCore.Results.Plato.Theaetetus.ConcessionDefeatsMeasure
