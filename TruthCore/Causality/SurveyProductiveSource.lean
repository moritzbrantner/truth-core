module

public import TruthCore.Causality.CausalPowerConcreteness
public import TruthCore.Causality.PossibleCausalSourceNecessity

/-! Analyst calibration of A2's existing actual-source route. No original
capability sense is completed. Production means the existing actual Causes
relation; it is not incoming capability or a cause of necessity. Same Ontic,
carrier and rigid individual throughout; no counterpart transport is hidden. -/

@[expose] public section
namespace TruthCore.Causality.SurveyProductiveSource
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.CausalPowerConcreteness

/-- OPEN: every existing uncaused candidate in a world accessible from w
actually produces something there. This excludes isolated sources; it neither
assumes concreteness nor asserts that any source exists. No endpoint existence
for the effect is included. The actualGraph cause endpoint is already actual. -/
def ProductiveSources {W B : Type} (m : Ontic W B) (w : W) : Prop :=
  ∀ v, m.frame.access w v → ∀ c, m.ExistsAt v c →
    (¬ ∃ y, m.ExistsAt v y ∧ m.Causes v y c) → ∃ y, m.Causes v c y

/-- OPEN: the existing direct-exercise concreteness clause holds at accessible
worlds for this SAME concrete predicate. We do not assume the desired necessary
concrete existential. IntendedProfile supplies this through exerciseHasPower
and powerConcrete; endpoint existence alone does not supply it. -/
def AccessibleCausersConcrete {W B : Type} (m : Ontic W B)
    (concrete : B → Prop) (w : W) : Prop :=
  ∀ v, m.frame.access w v → CausersRequireConcreteAt m concrete v

/-- Only the required dictionary fields are used; no grounding policy,
abstractness, or actual endpoint law is needed to classify a producing cause. -/
theorem intendedCalibration {W B : Type} (p : IntendedProfile W B) (w : W) :
    AccessibleCausersConcrete p.underlying.ontic p.underlying.concrete w :=
  fun v _ c y edge => p.powerConcrete v c (p.exerciseHasPower v c y edge)

/-- Finite audit family only, never a replacement for either original sense.
All candidates exist at the sole world. The optional edge is true to false. -/
def control (edge concrete : Prop) : BruteFoundationBoundary.Profile Unit Bool where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True,
             Causes := fun _ x y => edge ∧ x = true ∧ y = false }
  concrete := fun _ => concrete
  grounds := fun _ _ _ => False

/-- Two independent carrying-clause omissions and one joint witness.
The original four nonlogical modal/source inputs hold in each model, as
certified separately by controlBackground. Excluded middle is logical.
These models do not test counterpart transport or metaphysical possibility. -/
def Controls : Prop :=
  (AccessibleCausersConcrete (control False False).ontic (control False False).concrete () ∧
    ¬ ProductiveSources (control False False).ontic () ∧
    ¬ BruteFoundationBoundary.NecessaryConcreteAt (control False False) ()) ∧
  (ProductiveSources (control True False).ontic () ∧
    ¬ AccessibleCausersConcrete (control True False).ontic (control True False).concrete () ∧
    ¬ BruteFoundationBoundary.NecessaryConcreteAt (control True False) ()) ∧
  (ProductiveSources (control True True).ontic () ∧
    AccessibleCausersConcrete (control True True).ontic (control True True).concrete () ∧
    BruteFoundationBoundary.NecessaryConcreteAt (control True True) ())

end TruthCore.Causality.SurveyProductiveSource
