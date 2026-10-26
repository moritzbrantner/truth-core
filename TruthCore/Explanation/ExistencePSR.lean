import TruthCore.German.Kant.CosmologicalInference

/-!
Two finite, analyst-defined countermodels for the PSR scope question in #312.
The possible beings, accessibility, existence and causal relation reuse the
Ontic model from the Kant campaign. An explanation of an *existence fact* is
typed separately from a cause of an *individual*. Neither the admissibility
of an explanation token nor the models' logical consistency demonstrates the
metaphysical truth of the unrestricted PSR or of a necessary being.
-/
namespace TruthCore.Explanation.ExistencePSR

open TruthCore.German.Kant.CosmologicalInference

/-- A tagged existential fact; the object itself is not conflated with the
proposition that the object exists in the selected world. -/
inductive ExistenceFact (Being : Type) where
  | fact : Being → ExistenceFact Being

/-- Two stipulated explanatory candidates. The `intrinsic` tag is not a proof
that an essence really explains its own instantiation. -/
inductive Reason (Being : Type) where
  | intrinsic : Being → Reason Being
  | circumstance : Being → Reason Being

/-- The ontology and its ordinary causal relation stay intact; explanations
relate reason tokens to existence facts, not one being to another being. -/
structure Model (World Being : Type) where
  ontic : Ontic World Being
  explains : World → Reason Being → ExistenceFact Being → Prop

/-- No model may assign an explanation to an existence fact that is false at
the world in question. This is a modest soundness condition, not sufficiency. -/
def Sound (m : Model W E) : Prop :=
  ∀ w x r, m.explains w r (.fact x) → m.ontic.ExistsAt w x

/-- A candidate unrestricted *existence-fact* PSR (not all true facts). -/
def ExistencePSR (m : Model W E) : Prop :=
  ∀ w x, m.ontic.ExistsAt w x → ∃ r, m.explains w r (.fact x)

/-- A contingent-only existence PSR, using the existing de re modal scope. -/
def ContingentPSR (m : Model W E) : Prop :=
  ∀ w x, ContingentAt m.ontic w x → ∃ r, m.explains w r (.fact x)

/-- The separate *external cause for each existent* requirement. The
countermodel below refutes its derivability from `ExistencePSR` alone. -/
def EveryExistentExternallyCaused (m : Model W E) : Prop :=
  ∀ w x, m.ontic.ExistsAt w x →
    ∃ y, m.ontic.ExistsAt w y ∧ y ≠ x ∧ m.ontic.Causes w y x

/-- First model: a necessary actual individual has a stipulated intrinsic
reason at every world and no other being causes it. Second model: a genuinely
contingent individual's existence is explained, while a necessary individual's
existence is not. Hence contingent-only PSR does not suffice for the broader
existence-PSR even on a universally accessible frame. These are model-theoretic
separations, not claims that either explanation is metaphysically sufficient. -/
def PsrScopeBoundary : Prop :=
  (∃ m : Model Bool Bool,
    (∀ w v, m.ontic.frame.access w v) ∧
    Sound m ∧ ExistencePSR m ∧ NecessaryBeing m.ontic false ∧
    ¬ EveryExistentExternallyCaused m) ∧
  (∃ m : Model Bool Bool,
    (∀ w v, m.ontic.frame.access w v) ∧
    Sound m ∧ ContingentPSR m ∧
    ContingentAt m.ontic false true ∧ NecessaryBeing m.ontic false ∧
    ¬ ExistencePSR m)

end TruthCore.Explanation.ExistencePSR
