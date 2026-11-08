module

public import TruthCore.Causality.SuccessionPotency

@[expose] public section

namespace TruthCore.Results.Causality.SuccessionPotency
open TruthCore.Causality.SuccessionPotency
open TruthCore.Latin.Aquinas.SummaTheologiae (SuccessionRequiresPotencyReading)
open TruthCore.Greek.Aristotle.Physics (BeingMovedIsActualizationOfPotencyReading)

/-- A succession of life-states is a being moved, and whatever is being moved is
in potency in that respect. Conditional on two OPEN premises. -/
theorem successionRequiresPotency {B R T S : Type} [LT T]
    (InPotency MovedIn ActualizedQuaPotential : B → R → Prop)
    (LivesAt : B → T → Prop) (lifeStateAt : B → T → S)
    (hSuccession : SuccessionIsBeingMoved LivesAt lifeStateAt MovedIn)
    (hMotion : BeingMovedIsActualizationOfPotencyReading MovedIn InPotency ActualizedQuaPotential) :
    SuccessionRequiresPotencyReading InPotency LivesAt lifeStateAt := by
  intro x hx
  obtain ⟨r, hr⟩ := hSuccession x hx
  exact ⟨r, ((hMotion x r).mp hr).1⟩

section Controls
open TruthCore.Causality.SuccessionPotency.Control

theorem hasSuccession : TruthCore.Latin.Aquinas.SummaTheologiae.LifeHasSuccession lives state () :=
  ⟨false, true, rfl, trivial, trivial, Bool.noConfusion⟩

theorem controls : Certificate :=
  ⟨⟨fun h => (h () hasSuccession).elim (fun _ h => h),
      fun _ _ => ⟨fun h => h.elim, fun h => h.1.elim⟩,
      fun h => (h () hasSuccession).elim (fun _ h => h)⟩,
    ⟨fun _ _ => ⟨(), trivial⟩, fun h => ((h () ()).mp trivial).1,
      fun h => (h () hasSuccession).elim (fun _ h => h)⟩,
    ⟨fun _ _ => ⟨(), trivial⟩, fun _ _ => ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩,
      fun _ _ => ⟨(), trivial⟩⟩⟩

end Controls

end TruthCore.Results.Causality.SuccessionPotency
