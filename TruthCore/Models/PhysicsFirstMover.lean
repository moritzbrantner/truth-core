import TruthCore.Models.Physics

/-! Named finite interpretations and closed certificates for #414.
Registration tests formal consequence only; it does not establish metaphysical possibility.
Existing Challenges and proof obligations are unchanged. -/
namespace TruthCore.Models.PhysicsFirstMover
open TruthCore.Models.FiniteSupport
namespace NoSensibleMotion
def model : TruthCore.Models.Physics.Model where
  IsPhysicalRespect := fun _ => False
  MovedIn := fun _ _ => False
  ByNature := fun _ _ => False
  ByForce := fun _ _ => False
  SelfMovedIn := fun _ _ => False
  PassiveNaturalIn := fun _ _ => False
  InAct := fun _ _ => False
  InPotency := fun _ _ => False
  ActualizedQuaPotential := fun _ _ => False
  MovesIn := fun _ _ _ => False
  MovesPerAccidensIn := fun _ _ _ => False
theorem evaluation0 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (Unit) (Unit) (TruthCore.Models.PhysicsFirstMover.NoSensibleMotion.model.MovedIn)) := by unfold model TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading; decide

theorem evaluation1 : @TruthCore.Greek.Aristotle.Physics.Typed.EveryMovedThingHasSomeMoverReading (Unit) (Unit) (TruthCore.Models.PhysicsFirstMover.NoSensibleMotion.model.MovedIn) (TruthCore.Models.PhysicsFirstMover.NoSensibleMotion.model.MovesIn) := by unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryMovedThingHasSomeMoverReading; decide

theorem evaluation2 : @TruthCore.Greek.Aristotle.Physics.Typed.NoInfiniteSeriesOfMoversMovedByAnotherReading (Unit) (Unit) (TruthCore.Models.PhysicsFirstMover.NoSensibleMotion.model.MovesIn) := by
  exact fun x => Acc.intro x (fun _ ⟨_, ⟨_, hm⟩, _⟩ => hm.elim)

theorem evaluation3 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.FirstMoverNotMovedByAnotherCannotBeLackingReading (Unit) (Unit) (TruthCore.Models.PhysicsFirstMover.NoSensibleMotion.model.MovesIn)) := by
  intro h
  apply h
  rintro ⟨_, ⟨_, _, hm⟩, _⟩
  exact hm

end NoSensibleMotion
namespace MovedWithoutMover
def model : TruthCore.Models.Physics.Model where
  IsPhysicalRespect := fun _ => False
  MovedIn := fun _ _ => True
  ByNature := fun _ _ => False
  ByForce := fun _ _ => False
  SelfMovedIn := fun _ _ => False
  PassiveNaturalIn := fun _ _ => False
  InAct := fun _ _ => False
  InPotency := fun _ _ => False
  ActualizedQuaPotential := fun _ _ => False
  MovesIn := fun _ _ _ => False
  MovesPerAccidensIn := fun _ _ _ => False
theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (Unit) (Unit) (TruthCore.Models.PhysicsFirstMover.MovedWithoutMover.model.MovedIn) := by unfold model TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading; decide

theorem evaluation1 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.EveryMovedThingHasSomeMoverReading (Unit) (Unit) (TruthCore.Models.PhysicsFirstMover.MovedWithoutMover.model.MovedIn) (TruthCore.Models.PhysicsFirstMover.MovedWithoutMover.model.MovesIn)) := by unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryMovedThingHasSomeMoverReading; decide

theorem evaluation2 : @TruthCore.Greek.Aristotle.Physics.Typed.NoInfiniteSeriesOfMoversMovedByAnotherReading (Unit) (Unit) (TruthCore.Models.PhysicsFirstMover.MovedWithoutMover.model.MovesIn) := by
  exact fun x => Acc.intro x (fun _ ⟨_, ⟨_, hm⟩, _⟩ => hm.elim)

theorem evaluation3 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.FirstMoverNotMovedByAnotherCannotBeLackingReading (Unit) (Unit) (TruthCore.Models.PhysicsFirstMover.MovedWithoutMover.model.MovesIn)) := by
  intro h
  apply h
  rintro ⟨_, ⟨_, _, hm⟩, _⟩
  exact hm

end MovedWithoutMover
end TruthCore.Models.PhysicsFirstMover
