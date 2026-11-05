import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Cause
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting

/-!
Formal omission and compatibility controls for the five premises that derive
`CompositeHasAUnitingCauseReading` (result COMPOSITE-UNITING-CAUSE-FROM-UNION).
Each control is a stipulated finite interpretation of the shared vocabulary. It
shows what the encoded premises do and do not entail. It does not claim that any
interpretation is metaphysically possible, nor that a rival account is refuted.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting.Control
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting

/-- For each of the five premises, some interpretation satisfies the other four
while that premise and `CompositeHasAUnitingCauseReading` both fail. In the
first, the existing fifth-proof reading (a component other than itself) still
holds. A sixth interpretation satisfies all five with a composite present. -/
def Certificate : Prop :=
  -- 1. Without two distinct components: one component other than the composite.
  (∃ (B R : Type) (Composite : B → Prop) (ComponentOf : B → B → Prop)
      (Unites : B → B → B → B → Prop) (EfficientlyCausesIn CausesIn : B → B → R → Prop)
      (esse : R),
    ¬ CompositeHasTwoDistinctComponentsReading Composite ComponentOf ∧
    CompositeHasComponentOtherThanItselfReading Composite ComponentOf ∧
    DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf Unites ∧
    UnitingCauseIsEfficientCauseReading Unites EfficientlyCausesIn ∧
    UnitingCauseCausesBeingReading Unites CausesIn esse ∧
    NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn ∧
    ¬ CompositeHasAUnitingCauseReading Composite CausesIn esse) ∧
  -- 2. Without the uniting-cause principle: two components, no uniter.
  (∃ (B R : Type) (Composite : B → Prop) (ComponentOf : B → B → Prop)
      (Unites : B → B → B → B → Prop) (EfficientlyCausesIn CausesIn : B → B → R → Prop)
      (esse : R),
    CompositeHasTwoDistinctComponentsReading Composite ComponentOf ∧
    ¬ DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf Unites ∧
    UnitingCauseIsEfficientCauseReading Unites EfficientlyCausesIn ∧
    UnitingCauseCausesBeingReading Unites CausesIn esse ∧
    NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn ∧
    ¬ CompositeHasAUnitingCauseReading Composite CausesIn esse) ∧
  -- 3. Without uniter-is-efficient: the whole unites itself and causes its own
  -- being, but not efficiently.
  (∃ (B R : Type) (Composite : B → Prop) (ComponentOf : B → B → Prop)
      (Unites : B → B → B → B → Prop) (EfficientlyCausesIn CausesIn : B → B → R → Prop)
      (esse : R),
    CompositeHasTwoDistinctComponentsReading Composite ComponentOf ∧
    DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf Unites ∧
    ¬ UnitingCauseIsEfficientCauseReading Unites EfficientlyCausesIn ∧
    UnitingCauseCausesBeingReading Unites CausesIn esse ∧
    NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn ∧
    ¬ CompositeHasAUnitingCauseReading Composite CausesIn esse) ∧
  -- 4. Without uniter-causes-being: a distinct efficient uniter that causes
  -- nothing's being.
  (∃ (B R : Type) (Composite : B → Prop) (ComponentOf : B → B → Prop)
      (Unites : B → B → B → B → Prop) (EfficientlyCausesIn CausesIn : B → B → R → Prop)
      (esse : R),
    CompositeHasTwoDistinctComponentsReading Composite ComponentOf ∧
    DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf Unites ∧
    UnitingCauseIsEfficientCauseReading Unites EfficientlyCausesIn ∧
    ¬ UnitingCauseCausesBeingReading Unites CausesIn esse ∧
    NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn ∧
    ¬ CompositeHasAUnitingCauseReading Composite CausesIn esse) ∧
  -- 5. Without no-efficient-self-cause: the whole efficiently unites itself.
  (∃ (B R : Type) (Composite : B → Prop) (ComponentOf : B → B → Prop)
      (Unites : B → B → B → B → Prop) (EfficientlyCausesIn CausesIn : B → B → R → Prop)
      (esse : R),
    CompositeHasTwoDistinctComponentsReading Composite ComponentOf ∧
    DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf Unites ∧
    UnitingCauseIsEfficientCauseReading Unites EfficientlyCausesIn ∧
    UnitingCauseCausesBeingReading Unites CausesIn esse ∧
    ¬ NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn ∧
    ¬ CompositeHasAUnitingCauseReading Composite CausesIn esse) ∧
  -- 6. All five premises together, with a composite present.
  (∃ (B R : Type) (Composite : B → Prop) (ComponentOf : B → B → Prop)
      (Unites : B → B → B → B → Prop) (EfficientlyCausesIn CausesIn : B → B → R → Prop)
      (esse : R),
    CompositeHasTwoDistinctComponentsReading Composite ComponentOf ∧
    DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf Unites ∧
    UnitingCauseIsEfficientCauseReading Unites EfficientlyCausesIn ∧
    UnitingCauseCausesBeingReading Unites CausesIn esse ∧
    NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn ∧
    ∃ x, Composite x)

end TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting.Control
