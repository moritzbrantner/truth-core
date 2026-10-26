import TruthCore.Modal.NecessaryContingentActivity

/-!
Issue #462: even a necessarily existing cause that produces *some* effect at
every accessible world need not produce the *same* effect in every world.
The causal relation is world-indexed and says nothing about the sufficiency
of fixed antecedent conditions, free will, or metaphysical creation ex nihilo.
-/
namespace TruthCore.Modal.NecessaryVariableEffects

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.NecessaryContingentActivity

variable {World Being : Type}

/-- At every accessible world the source has at least one causal effect. -/
def NecessarilyCausesSomething (m : Ontic World Being) (w : World) (x : Being) : Prop :=
  ∀ v, m.frame.access w v → ∃ y, m.Causes v x y

/-- One *same* effect is caused at every accessible world. -/
def SameNecessaryEffect (m : Ontic World Being) (w : World) (x : Being) : Prop :=
  ∃ y, ∀ v, m.frame.access w v → m.Causes v x y

/-- A fixed necessary effect entails some effect at every accessible world. -/
theorem same_effect_implies_something (m : Ontic World Being) (w : World) (x : Being)
    (h : SameNecessaryEffect m w x) : NecessarilyCausesSomething m w x := by
  obtain ⟨y, hy⟩ := h
  intro v hv
  exact ⟨y, hy v hv⟩

/-- If the source's effects at two accessible worlds are disjoint, there
cannot be one particular effect caused at every accessible world. -/
theorem disjoint_effects_preclude_fixed
    (m : Ontic World Being) (w v₀ v₁ : World) (x : Being)
    (h₀ : m.frame.access w v₀) (h₁ : m.frame.access w v₁)
    (hDisjoint : ∀ y, m.Causes v₀ x y → ¬ m.Causes v₁ x y) :
    ¬ SameNecessaryEffect m w x := by
  rintro ⟨y, hy⟩
  exact hDisjoint y (hy v₀ h₀) (hy v₁ h₁)

/-- Three rigid possible individuals: one source and two distinct effects. -/
abbrev EffectBeing := Option Bool

def source : EffectBeing := none
def firstEffect : EffectBeing := some false
def secondEffect : EffectBeing := some true

/-- Finite carrier certificate for the registered interpretation. -/
theorem enumerateEffectBeing : ∀ x : EffectBeing,
    x = source ∨ x = firstEffect ∨ x = secondEffect := by
  intro x
  cases x with
  | none => exact Or.inl rfl
  | some b =>
    cases b with
    | false => exact Or.inr (Or.inl rfl)
    | true => exact Or.inr (Or.inr rfl)

/-- `none` is the source in both worlds. At world `w` its sole effect is
`some w`, which exists only at that world. Distinctness of the three candidate
beings is built into `Option Bool`, rather than assumed as an opaque premise. -/
def alternatingEffects : Ontic Bool EffectBeing where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun w x => x = none ∨ x = some w
  Causes := fun w x y => x = none ∧ y = some w

theorem effectsSound : SoundDistinctCauses alternatingEffects := by
  intro w x y h
  rcases h with ⟨rfl, rfl⟩
  refine ⟨Or.inl rfl, Or.inr rfl, ?_⟩
  intro h
  cases h

theorem sourceNecessary : NecessaryBeing alternatingEffects false := by
  refine ⟨none, Or.inl rfl, ?_⟩
  intro v _
  exact Or.inl rfl

theorem sourceNecessaryAt : NecessaryAt alternatingEffects false source := by
  intro v _
  exact Or.inl rfl

theorem alwaysCausesSomething :
    NecessarilyCausesSomething alternatingEffects false none := by
  intro v _
  exact ⟨some v, rfl, rfl⟩

theorem noFixedEffect :
    ¬ SameNecessaryEffect alternatingEffects false none := by
  rintro ⟨y, hy⟩
  have hFalse := hy false True.intro
  have hTrue := hy true True.intro
  have hDifferent : (some false : Option Bool) = some true :=
    hFalse.2.symm.trans hTrue.2
  cases hDifferent

/-- Control configuration: the same present effect is caused at both worlds.
This contrasts with `alternatingEffects` without changing the carrier, frame,
or distinct-existing-relata discipline. -/
def fixedEffects : Ontic Bool EffectBeing where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ x => x = source ∨ x = firstEffect
  Causes := fun _ x y => x = source ∧ y = firstEffect

theorem fixedEffectsSound : SoundDistinctCauses fixedEffects := by
  intro w x y h
  rcases h with ⟨rfl, rfl⟩
  refine ⟨Or.inl rfl, Or.inr rfl, ?_⟩
  intro h
  cases h

theorem fixedSourceNecessary : NecessaryBeing fixedEffects false := by
  exact ⟨source, Or.inl rfl, fun _ _ => Or.inl rfl⟩

theorem fixedSourceNecessaryAt : NecessaryAt fixedEffects false source := by
  intro _ _
  exact Or.inl rfl

theorem fixedSameNecessaryEffect :
    SameNecessaryEffect fixedEffects false source := by
  exact ⟨firstEffect, fun _ _ => ⟨rfl, rfl⟩⟩

theorem fixedAlwaysCausesSomething :
    NecessarilyCausesSomething fixedEffects false source :=
  same_effect_implies_something fixedEffects false source fixedSameNecessaryEffect

theorem fixedEffectNotContingent : ¬ ContingentAt fixedEffects false firstEffect := by
  rintro ⟨_, v, _, hNotExists⟩
  exact hNotExists (Or.inr rfl)

theorem firstEffectContingent :
    ContingentAt alternatingEffects false firstEffect := by
  refine ⟨Or.inr rfl, true, True.intro, ?_⟩
  rintro (h | h)
  · cases h
  · cases h

/-- Consistency of necessary source, ubiquitous causal exercise, contingent
recipient populations, and absence of a *single* necessary particular effect.
No inference to God, agency, determinism or free creation is encoded. -/
def NecessarySourceVariableEffects : Prop :=
  ∃ m : Ontic Bool (Option Bool),
    (∀ w v, m.frame.access w v) ∧
    SoundDistinctCauses m ∧ NecessaryBeing m false ∧
    NecessarilyCausesSomething m false none ∧
    ¬ SameNecessaryEffect m false none ∧
    ContingentAt m false (some false)

theorem necessarySourceVariableEffects : NecessarySourceVariableEffects := by
  refine ⟨alternatingEffects, ?_, effectsSound, sourceNecessary,
    alwaysCausesSomething, noFixedEffect, ?_⟩
  · intro _ _
    trivial
  · exact firstEffectContingent

end TruthCore.Modal.NecessaryVariableEffects
