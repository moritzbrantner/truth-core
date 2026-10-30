import TruthCore.Causality.TemporalActualization
namespace TruthCore.Results.Causality.TemporalActualization.Framework
open TruthCore.Causality.TemporalActualization

/-- Strictly increasing time on every edge also increases on every nonempty path. -/
theorem strict_acyclic {E T : Type} [Preorder T] (clock : E → T) (C : E → E → Prop)
    (h : StrictForward clock C) : EventAcyclic C := by
  have path {e f} (p : Relation.TransGen C e f) : clock e < clock f := by
    induction p with
    | single edge => exact h _ _ edge
    | tail _ edge ih => exact lt_trans ih (h _ _ edge)
  intro e cycle
  exact (lt_irrefl (clock e)) (path cycle)

/-- Linear order converts a non-strict, non-backward edge to a simultaneous one.
Classical quantifier negation is explicit in this analyst certificate. -/
theorem coverage {E T : Type} [LinearOrder T] (clock : E → T) (C : E → E → Prop) :
    DirectionFork clock C := by
  classical
  by_cases hBack : HasBackward clock C
  · exact Or.inr (Or.inr hBack)
  have hNB : NoBackward clock C := by
    intro e f edge rev
    exact hBack ⟨e, f, edge, rev⟩
  by_cases hStrict : StrictForward clock C
  · exact Or.inl hStrict
  right; left
  refine ⟨hNB, ?_⟩
  simp only [StrictForward, not_forall] at hStrict
  obtain ⟨e, f, edge, notBefore⟩ := hStrict
  exact ⟨e, f, edge, le_antisymm (le_of_not_gt (hNB e f edge)) (le_of_not_gt notBefore)⟩

/-- Incompatibility does not itself establish that any horn is instantiated. -/
theorem exclusive {E T : Type} [Preorder T] (clock : E → T) (C : E → E → Prop) :
    DirectionExclusive clock C := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hs, _, e, f, edge, eq⟩
    have hh := hs e f edge
    rw [eq] at hh
    exact lt_irrefl _ hh
  · rintro ⟨hs, e, f, edge, rev⟩
    exact lt_asymm (hs e f edge) rev
  · rintro ⟨⟨hn, _⟩, e, f, edge, rev⟩
    exact hn e f edge rev

/-- Exact coverage, separate exclusivity and the strict-forward acyclicity consequence. -/
theorem framework : TruthCore.Causality.TemporalActualization.Framework := by
  intro E T _ clock C
  exact ⟨coverage clock C, exclusive clock C, strict_acyclic clock C⟩
end TruthCore.Results.Causality.TemporalActualization.Framework
