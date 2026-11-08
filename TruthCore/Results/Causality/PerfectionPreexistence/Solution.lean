module

public import TruthCore.Causality.PerfectionPreexistence


@[expose] public section

namespace TruthCore.Results.Causality.PerfectionPreexistence
open TruthCore.Case.Catholicism (CauseOfBeingCausesEveryPerfection)
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (MoreSuchHasThePerfectionReading PerfectionsOfEffectPreexistInCauseReading)
open TruthCore.Logic (ExcludedMiddle)

/-- A cause of a thing's being, distinct from it, causes each of its perfections
and so is more such and has them; a self-cause has them trivially. Conditional on
four OPEN premises. -/
theorem preexistFromCausalTransfer {B R : Type} (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R)
    (hEM : ExcludedMiddle)
    (hTransfer : CauseOfBeingCausesEveryPerfection InAct CausesIn esse)
    (hMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hHas : MoreSuchHasThePerfectionReading InAct MoreIn) :
    PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse := by
  intro c x r hc hx
  rcases hEM (c = x) with hEq | hNe
  · exact hEq ▸ hx
  · exact hHas r c x (hMore c x r hNe (hTransfer c x r hc hx))

section Controls
open TruthCore.Causality.PerfectionPreexistence.Control

/-- The witness failure of preexistence: `true` causes `false`'s being,
`false` has the further perfection, `true` lacks it. -/
theorem noPreexist (C : Bool → Bool → Bool → Prop) (hC : C true false false) :
    ¬ PerfectionsOfEffectPreexistInCauseReading inAct C false :=
  fun h => (h true false true hC (Or.inr rfl)).elim Bool.noConfusion Bool.noConfusion

theorem controls : Certificate :=
  ⟨⟨fun h => (h true false true ⟨rfl, rfl, rfl⟩ (Or.inr rfl)).2.2 |> Bool.noConfusion,
      fun _ _ _ _ h => ⟨h.1, h.2.1, h.2.2⟩, fun _ _ _ h => Or.inl h.2.2,
      noPreexist _ ⟨rfl, rfl, rfl⟩⟩,
    ⟨fun _ _ _ h _ => h, fun h => h true false true Bool.noConfusion ⟨rfl, rfl⟩,
      fun _ _ _ h => h.elim, noPreexist _ ⟨rfl, rfl⟩⟩,
    ⟨fun _ _ _ h _ => h, fun _ _ _ _ h => h,
      fun h => (h true true false ⟨rfl, rfl⟩).elim Bool.noConfusion Bool.noConfusion,
      noPreexist _ ⟨rfl, rfl⟩⟩,
    ⟨fun _ _ _ h _ => h, fun _ _ _ _ h => h, fun _ _ _ _ => trivial,
      fun _ _ _ _ _ => trivial, ⟨rfl, rfl⟩⟩⟩

end Controls

end TruthCore.Results.Causality.PerfectionPreexistence
