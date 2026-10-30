import TruthCore.Results.Causality.TemporalActualization.Reciprocal.Solution
namespace TruthCore.Results.Causality.TemporalActualization.Controls
open TruthCore.Causality.TemporalActualization

theorem controls : TruthCore.Causality.TemporalActualization.Controls := by
  have forward : StrictForward (fun e : Fin 3 => (e.val : ℤ)) feedbackC := by
    intro e f edge
    change (e.val : ℤ) < (f.val : ℤ)
    simp only [feedbackC] at edge
    omega
  have infiniteForward : StrictForward (fun n : ℕ => -(n : ℤ)) (fun y x => y = x + 1) := by
    intro y x edge
    subst y
    change -((x + 1 : ℕ) : ℤ) < -(x : ℤ)
    omega
  have projection : MotionProjection circleClock id id circleC circleMoves := by
    intro e f edge
    exact ⟨rfl, edge, rfl⟩
  have located : LocatedMotion circleMoves circleMoved := by
    intro t y x r h
    exact ⟨h.1, h.2.2⟩
  have potential : PotentialMotion circleMoved circlePotency := by
    intro t x r h
    exact Or.inl h
  have actual : ActualMover circleMoves circleActual := by
    rintro t y x r ⟨ht, hne, hr⟩
    exact Or.inl ⟨ht, by simpa [hr] using Ne.symm hne⟩
  have notBoth : NotBoth circleActual circlePotency := by
    rintro t x r ⟨ha, hp⟩
    rcases ha with ⟨ht, hne⟩ | ht <;> rcases hp with ⟨ht', heq⟩ | ht'
    · exact hne heq
    all_goals omega
  have noBack : NoBackward circleClock circleC := by
    intro e f _
    exact lt_irrefl 0
  have pred (e : Bool) : ∃ f, circleC f e := by
    cases e <;> simp [circleC]
  refine ⟨⟨forward, Framework.strict_acyclic _ _ forward, ?_, ?_⟩,
    ⟨noBack, ?_, ?_, ?_, projection, located, potential, actual, notBoth,
      Reciprocal.consume circleClock id id circleC circleMoves circleMoved circleActual circlePotency
        noBack projection located potential actual notBoth, pred, ?_⟩,
    ?_, ⟨infiniteForward, Framework.strict_acyclic _ _ infiniteForward, ?_⟩, ?_,
    TruthCore.Results.Causality.TemporalEventControls.controls⟩
  · exact ⟨0, 1, rfl, rfl, rfl⟩
  · exact ⟨1, 2, rfl, rfl, rfl⟩
  · exact ⟨false, true, by simp [circleC], rfl⟩
  · intro h
    exact lt_irrefl 0 (h false true (by simp [circleC]))
  · intro h
    exact h false ((Relation.TransGen.single (show circleC false true by simp [circleC])).trans
      (Relation.TransGen.single (show circleC true false by simp [circleC])))
  · refine ⟨circleC, rfl, ?_, ?_⟩
    · intro e
      exact ⟨fun _ => let ⟨f, hf⟩ := pred e; ⟨f, hf, trivial⟩, fun _ => trivial⟩
    · intro e
      exact ⟨False.elim, fun ⟨_, _, hf⟩ => hf⟩
  · exact ⟨true, false, by simp [circleC], by decide⟩
  · intro hw
    exact TruthCore.Causality.successorChainNotWellFounded hw.apply
  · refine ⟨?_, by simp [circleC], by decide⟩
    intro e
    exact ⟨by norm_num [circleClock], by norm_num [circleClock],
      Or.inr (by norm_num), Or.inr (by norm_num)⟩
end TruthCore.Results.Causality.TemporalActualization.Controls
