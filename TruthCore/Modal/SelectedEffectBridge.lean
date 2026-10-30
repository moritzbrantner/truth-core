import TruthCore.Modal.NecessaryVariableEffects

/-! Analyst-defined output controls for #462. An act is a rigid token, not a
metaphysical analysis of willing. Local output uniqueness does not impose
cross-world output identity. Existing causal/existence tables are unchanged. -/
namespace TruthCore.Modal.SelectedEffectBridge
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.NecessaryContingentActivity
open TruthCore.Modal.NecessaryVariableEffects

/-- Minimal act-output overlay. `performs` and `output` are separate primitive
assignments; the laws below are explicit obligations, not structure fields. -/
structure OutputProfile (W B A : Type) where
  ontic : Ontic W B
  source : B
  performs : W → A → Prop
  output : W → A → B → Prop

/-- A given act has at most one output at each world. This permits different
outputs at different worlds and does not guarantee any output. -/
def LocallyDeterministic (p : OutputProfile W B A) : Prop :=
  ∀ v a x y, p.output v a x → p.output v a y → x = y

/-- The same selected act token is performed at every accessible world. -/
def SameActEverywhere (p : OutputProfile W B A) (w : W) (a : A) : Prop :=
  ∀ v, p.ontic.frame.access w v → p.performs v a

/-- An actual selected output recurs wherever this act is performed at an
accessible world. This is cross-world sufficiency, beyond local uniqueness. -/
def StableActOutput (p : OutputProfile W B A) (w : W) (a : A) : Prop :=
  ∀ x, p.output w a x → ∀ v, p.ontic.frame.access w v →
    p.performs v a → p.output v a x

/-- Outputs of performed acts are causal edges of the selected source. -/
def RealizedOutputs (p : OutputProfile W B A) : Prop :=
  ∀ v a x, p.performs v a → p.output v a x →
    p.ontic.Causes v p.source x

/-- Reuse the alternating-effects ontology; the sole act is performed in both
worlds and has exactly one output, selected by the world label. -/
def varying : OutputProfile Bool EffectBeing Unit where
  ontic := alternatingEffects
  source := source
  performs := fun _ _ => True
  output := fun w _ x => x = some w

/-- A deterministic law on the full condition `c` can still vary its output
when `c` varies between worlds. The law itself is world-independent. -/
def conditionedOutput (c : Bool) : EffectBeing := some c

/-- Closed package: stable output plus ubiquitous same-act performance and
sound causal realization entails the particular effect's necessity. Fixed
full conditions plus a fixed output function suffice for stable output.
The unchanged alternating model satisfies same-act/local-determinism but
violates stability and retains a contingent particular effect. -/
def SelectedEffectCertificate : Prop :=
  (∀ (W B A : Type) (p : OutputProfile W B A) (w : W) (a : A) (x : B),
    SoundDistinctCauses p.ontic → RealizedOutputs p →
    SameActEverywhere p w a → StableActOutput p w a → p.output w a x →
    NecessaryAt p.ontic w x) ∧
  (∀ (W B A C : Type) (p : OutputProfile W B A) (w : W) (a : A)
      (condition : W → C) (response : C → B),
    (∀ v, p.ontic.frame.access w v → condition v = condition w) →
    (∀ v x, p.output v a x ↔ x = response (condition v)) →
    StableActOutput p w a) ∧
  (SoundDistinctCauses varying.ontic ∧
    NecessaryAt varying.ontic false varying.source ∧
    RealizedOutputs varying ∧ SameActEverywhere varying false () ∧
    LocallyDeterministic varying ∧
    (∀ v x, varying.output v () x ↔ x = conditionedOutput v) ∧
    ¬ StableActOutput varying false () ∧
    NecessarilyCausesSomething varying.ontic false varying.source ∧
    ¬ SameNecessaryEffect varying.ontic false varying.source ∧
    ContingentAt varying.ontic false firstEffect)
end TruthCore.Modal.SelectedEffectBridge
