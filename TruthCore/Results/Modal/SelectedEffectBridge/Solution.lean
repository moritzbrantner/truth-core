import TruthCore.Modal.SelectedEffectBridge
namespace TruthCore.Results.Modal.SelectedEffectBridge
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.NecessaryContingentActivity
open TruthCore.Modal.NecessaryVariableEffects
open TruthCore.Modal.SelectedEffectBridge

theorem selectedEffectNecessary (p : OutputProfile W B A) (w : W) (a : A) (x : B)
    (hSound : SoundDistinctCauses p.ontic) (hRealized : RealizedOutputs p)
    (hSame : SameActEverywhere p w a) (hStable : StableActOutput p w a)
    (hActual : p.output w a x) : NecessaryAt p.ontic w x := by
  intro v hv
  exact (hSound v p.source x
    (hRealized v a x (hSame v hv) (hStable x hActual v hv (hSame v hv)))).2.1

theorem fixedConditionsStable (p : OutputProfile W B A) (w : W) (a : A)
    (condition : W → C) (response : C → B)
    (hFixed : ∀ v, p.ontic.frame.access w v → condition v = condition w)
    (hLaw : ∀ v x, p.output v a x ↔ x = response (condition v)) :
    StableActOutput p w a := by
  intro x hx v hv _
  apply (hLaw v x).mpr
  rw [hFixed v hv]
  exact (hLaw w x).mp hx

theorem varyingChecks :
    SoundDistinctCauses varying.ontic ∧
    NecessaryAt varying.ontic false varying.source ∧
    RealizedOutputs varying ∧ SameActEverywhere varying false () ∧
    LocallyDeterministic varying ∧
    (∀ v x, varying.output v () x ↔ x = conditionedOutput v) ∧
    ¬ StableActOutput varying false () ∧
    NecessarilyCausesSomething varying.ontic false varying.source ∧
    ¬ SameNecessaryEffect varying.ontic false varying.source ∧
    ContingentAt varying.ontic false firstEffect := by
  refine ⟨effectsSound, sourceNecessaryAt, ?_, ?_, ?_, ?_, ?_,
    alwaysCausesSomething, noFixedEffect, firstEffectContingent⟩
  · intro v a x _ hx
    exact ⟨rfl, hx⟩
  · intro _ _
    trivial
  · intro v a x y hx hy
    exact hx.trans hy.symm
  · intro _ _
    exact Iff.rfl
  · intro h
    have hBad := h firstEffect rfl true True.intro True.intro
    cases hBad

theorem checks : SelectedEffectCertificate := by
  exact ⟨fun _ _ _ p w a x => selectedEffectNecessary p w a x,
    fun _ _ _ _ p w a c r => fixedConditionsStable p w a c r, varyingChecks⟩
end TruthCore.Results.Modal.SelectedEffectBridge
