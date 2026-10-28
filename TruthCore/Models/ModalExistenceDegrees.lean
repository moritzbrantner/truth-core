import TruthCore.Modal.NecessaryVariableEffects
import TruthCore.Models.OrderSecondary
import TruthCore.Modal.ExistenceDegrees

/-! Finite and infinite controls for a separately declared modal weak-bound profile.
The finite controls reuse ordered `Fin 3` intensity labels; the infinite
control uses ordered Nat labels. Neither is an existence truth value or count
of worlds. `ExistsAt` remains an independent world-indexed
predicate. The unused second effect is absent in these interpretations; its
assigned intensity is ignored by the existence-guarded comparisons.

The original fixed-effects interpretation is reused unchanged wherever
possible. The empty-cause variant is separate data, not an edit to that model.
All interpretations have rigid candidate identities and universal accessibility.
These are formal controls, not claims of metaphysical possibility or a
formalization of the whole Koons argument. -/
namespace TruthCore.Models.ModalExistenceDegrees

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.NecessaryVariableEffects
open TruthCore.Modal.NecessaryContingentActivity
open TruthCore.Modal.ExistenceDegrees
open TruthCore.Causality.NecessarilyUnderived

abbrev Intensity := TruthCore.Models.OrderSecondary.Degree
abbrev intensityOrder := TruthCore.Models.OrderSecondary.order
abbrev low := TruthCore.Models.OrderSecondary.d0
abbrev high := TruthCore.Models.OrderSecondary.d2

namespace TiedNecessary
abbrev ontic := fixedEffects
def intensity (_ : Bool) (x : EffectBeing) : Intensity :=
  if x = secondEffect then low else high
def model := (ontic, intensity)
end TiedNecessary

namespace VaryingDegree
abbrev ontic := fixedEffects
def intensity (w : Bool) (x : EffectBeing) : Intensity :=
  if x = secondEffect then low else if w then high else low
def model := (ontic, intensity)
end VaryingDegree

namespace BelowEffect
abbrev ontic := fixedEffects
def intensity (_ : Bool) (x : EffectBeing) : Intensity :=
  if x = firstEffect then high else low
def model := (ontic, intensity)
end BelowEffect

namespace NoPotential
def ontic : Ontic Bool EffectBeing where
  frame := fixedEffects.frame
  ExistsAt := fixedEffects.ExistsAt
  Causes := fun _ _ _ => False
abbrev intensity := BelowEffect.intensity
def model := (ontic, intensity)
end NoPotential

namespace PotentialOnly
def ontic : Ontic Bool EffectBeing where
  frame := fixedEffects.frame
  ExistsAt := fixedEffects.ExistsAt
  Causes := fun w x y => w = true ∧ fixedEffects.Causes w x y
abbrev intensity := TiedNecessary.intensity
def model := (ontic, intensity)
end PotentialOnly

local instance : Preorder Intensity := intensityOrder

private instance effectForall {p : EffectBeing → Prop} [DecidablePred p] :
    Decidable (∀ x, p x) :=
  decidable_of_iff (p source ∧ p firstEffect ∧ p secondEffect)
    ⟨fun h x => by
      rcases enumerateEffectBeing x with hx | hx | hx
      · exact hx.symm ▸ h.1
      · exact hx.symm ▸ h.2.1
      · exact hx.symm ▸ h.2.2,
     fun h => ⟨h source, h firstEffect, h secondEffect⟩⟩

private instance effectExists {p : EffectBeing → Prop} [DecidablePred p] :
    Decidable (∃ x, p x) :=
  decidable_of_iff (p source ∨ p firstEffect ∨ p secondEffect)
    ⟨fun h => h.elim (fun h => ⟨source, h⟩)
      (fun h => h.elim (fun h => ⟨firstEffect, h⟩) (fun h => ⟨secondEffect, h⟩)),
     fun ⟨x, h⟩ => by
      rcases enumerateEffectBeing x with hx | hx | hx
      · exact Or.inl (hx ▸ h)
      · exact Or.inr (Or.inl (hx ▸ h))
      · exact Or.inr (Or.inr (hx ▸ h))⟩

/- The finite search helper unfolds only the displayed profile and frozen
interpretations, then asks Lean's kernel-reduced decision procedure. -/
local macro "finite_modal_degree" : tactic => `(tactic| (
  dsimp only [PossibleCauseAt, OtherDirectedPotentialCause, WeakCauseDegreeBound,
    NecessaryDegreeInvariant, NecessaryGlobalDegreeMaximum, AttainedGlobalDegreeMaximum,
    NecessaryAt, ActualReflexive, SoundDistinctCauses, ExercisesCausation,
    TiedNecessary.ontic, TiedNecessary.intensity, VaryingDegree.ontic,
    VaryingDegree.intensity, BelowEffect.ontic, BelowEffect.intensity,
    NoPotential.ontic, NoPotential.intensity, PotentialOnly.ontic, PotentialOnly.intensity,
    fixedEffects, source, firstEffect, secondEffect, low, high, intensityOrder,
    TruthCore.Models.OrderSecondary.order, TruthCore.Models.OrderSecondary.finiteOrder,
    TruthCore.Models.OrderSecondary.d0, TruthCore.Models.OrderSecondary.d2] <;>
  decide))

namespace TiedNecessary
theorem sound : SoundDistinctCauses ontic := fixedEffectsSound

theorem reflexive : ActualReflexive ontic false := by finite_modal_degree

theorem necessary : NecessaryAt ontic false source := fixedSourceNecessaryAt

theorem potential : OtherDirectedPotentialCause ontic false source := by finite_modal_degree

theorem bound : WeakCauseDegreeBound ontic intensity false := by finite_modal_degree

theorem invariant : NecessaryDegreeInvariant ontic intensity false source := by finite_modal_degree

theorem maximum : NecessaryGlobalDegreeMaximum ontic intensity false source := by finite_modal_degree

/-- Distinct necessary individuals tie at the global maximum. This does not
say that both satisfy the universal possible-causer role. -/
theorem otherNecessaryMaximum :
    NecessaryAt ontic false firstEffect ∧
    NecessaryGlobalDegreeMaximum ontic intensity false firstEffect ∧
    firstEffect ≠ source := by finite_modal_degree

end TiedNecessary

namespace VaryingDegree
theorem sound : SoundDistinctCauses ontic := fixedEffectsSound

theorem reflexive : ActualReflexive ontic false := by finite_modal_degree

theorem necessary : NecessaryAt ontic false source := fixedSourceNecessaryAt

theorem potential : OtherDirectedPotentialCause ontic false source := by finite_modal_degree

theorem bound : WeakCauseDegreeBound ontic intensity false := by finite_modal_degree

theorem notInvariant : ¬ NecessaryDegreeInvariant ontic intensity false source := by finite_modal_degree

theorem notMaximum : ¬ NecessaryGlobalDegreeMaximum ontic intensity false source := by finite_modal_degree

/-- A possible attained maximum exists despite failure of the named source's
maximum at every world. This says nothing about a value/existence bridge. -/
theorem attainedMaximum : AttainedGlobalDegreeMaximum ontic intensity false := by
  finite_modal_degree

end VaryingDegree

namespace BelowEffect
theorem sound : SoundDistinctCauses ontic := fixedEffectsSound

theorem reflexive : ActualReflexive ontic false := by finite_modal_degree

theorem necessary : NecessaryAt ontic false source := fixedSourceNecessaryAt

theorem potential : OtherDirectedPotentialCause ontic false source := by finite_modal_degree

theorem notBound : ¬ WeakCauseDegreeBound ontic intensity false := by finite_modal_degree

theorem invariant : NecessaryDegreeInvariant ontic intensity false source := by finite_modal_degree

theorem notMaximum : ¬ NecessaryGlobalDegreeMaximum ontic intensity false source := by finite_modal_degree

end BelowEffect

namespace NoPotential
theorem sound : SoundDistinctCauses ontic := by finite_modal_degree

theorem reflexive : ActualReflexive ontic false := by finite_modal_degree

theorem necessary : NecessaryAt ontic false source := fixedSourceNecessaryAt

theorem notPotential : ¬ OtherDirectedPotentialCause ontic false source := by finite_modal_degree

theorem bound : WeakCauseDegreeBound ontic intensity false := by finite_modal_degree

theorem invariant : NecessaryDegreeInvariant ontic intensity false source := by finite_modal_degree

theorem notMaximum : ¬ NecessaryGlobalDegreeMaximum ontic intensity false source := by finite_modal_degree

end NoPotential

namespace PotentialOnly
theorem sound : SoundDistinctCauses ontic :=
  fun w x y h => fixedEffectsSound w x y h.2

theorem reflexive : ActualReflexive ontic false := by finite_modal_degree

theorem necessary : NecessaryAt ontic false source := fixedSourceNecessaryAt

theorem potential : OtherDirectedPotentialCause ontic false source := by finite_modal_degree

theorem bound : WeakCauseDegreeBound ontic intensity false := by finite_modal_degree

theorem invariant : NecessaryDegreeInvariant ontic intensity false source := by finite_modal_degree

theorem maximum : NecessaryGlobalDegreeMaximum ontic intensity false source := by finite_modal_degree

/-- Possibility at the standpoint does not imply actual causal exercise
there. The Boolean world labels are alternatives, not times. -/
theorem noActualExercise : ¬ ExercisesCausation ontic false source := by
  finite_modal_degree

end PotentialOnly

/- The source-supported actual-presence guard is kept separate from the bare
analyst condition. The fixed reflexive controls satisfy both antecedents. -/
namespace TiedNecessary
theorem actualInvariant : ActualNecessaryDegreeInvariant ontic intensity false source :=
  fun h => invariant h.2
end TiedNecessary

namespace VaryingDegree
theorem notActualInvariant :
    ¬ ActualNecessaryDegreeInvariant ontic intensity false source :=
  fun h => notInvariant (fun hn => h ⟨hn false trivial, hn⟩)
end VaryingDegree

namespace BelowEffect
theorem actualInvariant : ActualNecessaryDegreeInvariant ontic intensity false source :=
  fun h => invariant h.2
end BelowEffect

namespace NoPotential
theorem actualInvariant : ActualNecessaryDegreeInvariant ontic intensity false source :=
  fun h => invariant h.2
end NoPotential

namespace PotentialOnly
theorem actualInvariant : ActualNecessaryDegreeInvariant ontic intensity false source :=
  fun h => invariant h.2
end PotentialOnly

/-! An infinite control of possible attainment. Natural-number worlds are
alternative labels, not times or numbers of worlds. Each world has the same
necessary source/effect population and actual causal edge. Intensity varies
with the label although the accessible family and presence facts do not. -/
namespace UnboundedWorlds
def ontic : Ontic Nat EffectBeing where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ x => fixedEffects.ExistsAt false x
  Causes := fun _ x y => fixedEffects.Causes false x y

def intensity (w : Nat) (_ : EffectBeing) : Nat := w

/-- Full nonlogical modal/causal background except degree invariance, together
with failure even of some attained global degree maximum. No degree is compared
as an existence truth value, and absent candidates are existence-guarded. -/
def JointWitness : Prop :=
  (∀ w v, ontic.frame.access w v) ∧
  ActualReflexive ontic 0 ∧ ontic.ExistsAt 0 source ∧
  NecessaryAt ontic 0 source ∧ SoundDistinctCauses ontic ∧
  OtherDirectedPotentialCause ontic 0 source ∧
  WeakCauseDegreeBound ontic intensity 0 ∧
  ¬ NecessaryDegreeInvariant ontic intensity 0 source ∧
  ¬ ActualNecessaryDegreeInvariant ontic intensity 0 source ∧
  ¬ AttainedGlobalDegreeMaximum ontic intensity 0

theorem allAccess : ∀ w v, ontic.frame.access w v := fun _ _ => trivial

theorem reflexive : ActualReflexive ontic 0 := trivial

theorem actual : ontic.ExistsAt 0 source := Or.inl rfl

theorem necessary : NecessaryAt ontic 0 source := fun _ _ => Or.inl rfl

theorem sound : SoundDistinctCauses ontic :=
  fun _ x y h => fixedEffectsSound false x y h

theorem actualEdgeEveryWorld : ∀ w, ontic.Causes w source firstEffect :=
  fun _ => ⟨rfl, rfl⟩

theorem potential : OtherDirectedPotentialCause ontic 0 source := by
  intro v _ y hy hne
  change y = source ∨ y = firstEffect at hy
  rcases hy with hSource | hEffect
  · exact (hne hSource).elim
  · exact ⟨v, trivial, rfl, hEffect⟩

theorem bound : WeakCauseDegreeBound ontic intensity 0 :=
  fun v _ _ _ _ _ _ => Nat.le_refl v

theorem notInvariant : ¬ NecessaryDegreeInvariant ontic intensity 0 source :=
  fun h => (by decide : ¬ ((1 : Nat) ≤ 0)) ((h necessary) 1 trivial).1

theorem notActualInvariant : ¬ ActualNecessaryDegreeInvariant ontic intensity 0 source :=
  fun h => (by decide : ¬ ((1 : Nat) ≤ 0)) (h ⟨actual, necessary⟩ 1 trivial).1

/-- Every candidate maximum at v is exceeded by the existing source at v+1.
The comparison is across alternative worlds, not successive moments. -/
theorem noAttainedMaximum : ¬ AttainedGlobalDegreeMaximum ontic intensity 0 := by
  intro ⟨v, x, _, _, hBound⟩
  have hBad := hBound (v + 1) trivial source (Or.inl rfl)
  exact Nat.not_succ_le_self v hBad

theorem jointWitness : JointWitness :=
  ⟨allAccess, reflexive, actual, necessary, sound, potential, bound,
    notInvariant, notActualInvariant, noAttainedMaximum⟩
end UnboundedWorlds

end TruthCore.Models.ModalExistenceDegrees
