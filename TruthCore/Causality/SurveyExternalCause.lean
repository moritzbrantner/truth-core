module

/-!
The exclusion content of the NecessaryBeing A1c2 external-cause gloss.
The carrier, causal relation and parthood relation are supplied independently.
No temporal, modal, concreteness or actual-existence interpretation is imposed.
In particular this is not nonoverlap: sharing a part is not excluded.
-/

@[expose] public section

namespace TruthCore.Causality.SurveyExternalCause

/-- A particular source causes the selected thing and is distinct from that
thing and every one of its parts. Parthood may be proper or reflexive: explicit
self-exclusion is retained either way. Neither relation has structural laws
here. This defines externality of a cause, not existence of an external cause
for every contingent thing, or necessity of the selected source. -/
def ExternalCause {B : Type} (cause part : B → B → Prop) (c whole : B) : Prop :=
  cause c whole ∧ c ≠ whole ∧ ∀ p, part p whole → c ≠ p

/-- Nonvacuity control only; the general definition is not restricted to Bool. -/
example : ExternalCause (fun c x : Bool => c = true ∧ x = false)
    (fun p x => p = x) true false := by
  refine ⟨⟨rfl, rfl⟩, Bool.noConfusion, ?_⟩
  intro p hp heq
  exact Bool.noConfusion (heq.trans hp)

/-- Numerical distinction alone does not exclude being a part. -/
example : ¬ ExternalCause (fun _ _ : Bool => True)
    (fun _ _ => True) true false := by
  intro h
  exact h.2.2 true trivial rfl

/-- Self-causation fails even when the supplied proper-part relation is empty. -/
example : ¬ ExternalCause (fun _ _ : Bool => True)
    (fun _ _ => False) true true := by
  intro h
  exact h.2.1 rfl

end TruthCore.Causality.SurveyExternalCause
