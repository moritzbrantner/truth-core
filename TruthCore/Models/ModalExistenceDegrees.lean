import TruthCore.Modal.NecessaryVariableEffects
import TruthCore.Models.OrderSecondary
import TruthCore.Modal.ExistenceDegrees

/-! Finite controls for a separately declared modal weak-bound profile.
Intensity labels are the existing ordered `Fin 3` labels, not existence truth
values or counts of worlds. `ExistsAt` remains an independent world-indexed
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

end TruthCore.Models.ModalExistenceDegrees
