import TruthCore.Models.FiniteSupport
import TruthCore.Greek.Aristotle.Physics
import TruthCore.Greek.Aristotle.Physics.Typed.Motion

/-! Named finite interpretations and closed certificates for #414.
Registration tests formal consequence only; it does not establish metaphysical possibility.
Existing Challenges and proof obligations are unchanged. -/
namespace TruthCore.Models.Physics
open TruthCore.Models.FiniteSupport
structure Model where
  IsPhysicalRespect : Unit → Prop
  MovedIn : Unit → Unit → Prop
  ByNature : Unit → Unit → Prop
  ByForce : Unit → Unit → Prop
  SelfMovedIn : Unit → Unit → Prop
  PassiveNaturalIn : Unit → Unit → Prop
  InAct : Unit → Unit → Prop
  InPotency : Unit → Unit → Prop
  ActualizedQuaPotential : Unit → Unit → Prop
  MovesIn : Unit → Unit → Unit → Prop
  MovesPerAccidensIn : Unit → Unit → Unit → Prop

namespace PhysicalWithoutDivision
def model : Model where
  IsPhysicalRespect := fun _ => True
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
theorem evaluation0 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.EveryMotionNaturalOrForcedReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.IsPhysicalRespect) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.MovedIn) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.ByNature) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.ByForce)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryMotionNaturalOrForcedReading
  decide

theorem evaluation1 : @TruthCore.Greek.Aristotle.Physics.Typed.NaturalMotionSelfOrPassiveReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.ByNature) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.SelfMovedIn) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.PassiveNaturalIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.NaturalMotionSelfOrPassiveReading
  decide

theorem evaluation2 : @TruthCore.Greek.Aristotle.Physics.Typed.ForcedMotionByAnotherReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.ByForce) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.MovesIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.ForcedMotionByAnotherReading
  decide

theorem evaluation3 : @TruthCore.Greek.Aristotle.Physics.Typed.NaturalSelfMotionByAMoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.ByNature) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.SelfMovedIn) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.MovesIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.NaturalSelfMotionByAMoverReading
  decide

theorem evaluation4 : @TruthCore.Greek.Aristotle.Physics.Typed.PassiveNaturalMotionByGeneratorOrRemoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.PassiveNaturalIn) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.MovesIn) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.MovesPerAccidensIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.PassiveNaturalMotionByGeneratorOrRemoverReading
  decide

theorem evaluation5 : @TruthCore.Greek.Aristotle.Physics.Typed.PerAccidensMovedPassiveMotionHasPerSeMoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.PassiveNaturalIn) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.MovesIn) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.MovesPerAccidensIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.PerAccidensMovedPassiveMotionHasPerSeMoverReading
  decide

theorem evaluation6 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.EveryPhysicalMotionHasAPerSeMoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.IsPhysicalRespect) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.MovedIn) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.MovesIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryPhysicalMotionHasAPerSeMoverReading
  decide

theorem evaluation7 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.EveryMovedThingMovedPerSeOrPerAccidensReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.IsPhysicalRespect) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.MovedIn) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.MovesIn) (TruthCore.Models.Physics.PhysicalWithoutDivision.model.MovesPerAccidensIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryMovedThingMovedPerSeOrPerAccidensReading
  decide

end PhysicalWithoutDivision
namespace PhysicalWithoutNatural
def model : Model where
  IsPhysicalRespect := fun _ => True
  MovedIn := fun _ _ => True
  ByNature := fun _ _ => True
  ByForce := fun _ _ => False
  SelfMovedIn := fun _ _ => False
  PassiveNaturalIn := fun _ _ => False
  InAct := fun _ _ => False
  InPotency := fun _ _ => False
  ActualizedQuaPotential := fun _ _ => False
  MovesIn := fun _ _ _ => False
  MovesPerAccidensIn := fun _ _ _ => False
theorem evaluation0 : @TruthCore.Greek.Aristotle.Physics.Typed.EveryMotionNaturalOrForcedReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.IsPhysicalRespect) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.MovedIn) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.ByNature) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.ByForce) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryMotionNaturalOrForcedReading
  decide

theorem evaluation1 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.NaturalMotionSelfOrPassiveReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.ByNature) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.SelfMovedIn) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.PassiveNaturalIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.NaturalMotionSelfOrPassiveReading
  decide

theorem evaluation2 : @TruthCore.Greek.Aristotle.Physics.Typed.ForcedMotionByAnotherReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.ByForce) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.MovesIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.ForcedMotionByAnotherReading
  decide

theorem evaluation3 : @TruthCore.Greek.Aristotle.Physics.Typed.NaturalSelfMotionByAMoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.ByNature) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.SelfMovedIn) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.MovesIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.NaturalSelfMotionByAMoverReading
  decide

theorem evaluation4 : @TruthCore.Greek.Aristotle.Physics.Typed.PassiveNaturalMotionByGeneratorOrRemoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.PassiveNaturalIn) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.MovesIn) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.MovesPerAccidensIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.PassiveNaturalMotionByGeneratorOrRemoverReading
  decide

theorem evaluation5 : @TruthCore.Greek.Aristotle.Physics.Typed.PerAccidensMovedPassiveMotionHasPerSeMoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.PassiveNaturalIn) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.MovesIn) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.MovesPerAccidensIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.PerAccidensMovedPassiveMotionHasPerSeMoverReading
  decide

theorem evaluation6 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.EveryPhysicalMotionHasAPerSeMoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.IsPhysicalRespect) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.MovedIn) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.MovesIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryPhysicalMotionHasAPerSeMoverReading
  decide

theorem evaluation7 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.EveryMovedThingMovedPerSeOrPerAccidensReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.IsPhysicalRespect) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.MovedIn) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.MovesIn) (TruthCore.Models.Physics.PhysicalWithoutNatural.model.MovesPerAccidensIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryMovedThingMovedPerSeOrPerAccidensReading
  decide

end PhysicalWithoutNatural
namespace PhysicalWithoutForced
def model : Model where
  IsPhysicalRespect := fun _ => True
  MovedIn := fun _ _ => True
  ByNature := fun _ _ => False
  ByForce := fun _ _ => True
  SelfMovedIn := fun _ _ => False
  PassiveNaturalIn := fun _ _ => False
  InAct := fun _ _ => False
  InPotency := fun _ _ => False
  ActualizedQuaPotential := fun _ _ => False
  MovesIn := fun _ _ _ => False
  MovesPerAccidensIn := fun _ _ _ => False
theorem evaluation0 : @TruthCore.Greek.Aristotle.Physics.Typed.EveryMotionNaturalOrForcedReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutForced.model.IsPhysicalRespect) (TruthCore.Models.Physics.PhysicalWithoutForced.model.MovedIn) (TruthCore.Models.Physics.PhysicalWithoutForced.model.ByNature) (TruthCore.Models.Physics.PhysicalWithoutForced.model.ByForce) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryMotionNaturalOrForcedReading
  decide

theorem evaluation1 : @TruthCore.Greek.Aristotle.Physics.Typed.NaturalMotionSelfOrPassiveReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutForced.model.ByNature) (TruthCore.Models.Physics.PhysicalWithoutForced.model.SelfMovedIn) (TruthCore.Models.Physics.PhysicalWithoutForced.model.PassiveNaturalIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.NaturalMotionSelfOrPassiveReading
  decide

theorem evaluation2 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.ForcedMotionByAnotherReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutForced.model.ByForce) (TruthCore.Models.Physics.PhysicalWithoutForced.model.MovesIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.ForcedMotionByAnotherReading
  decide

theorem evaluation3 : @TruthCore.Greek.Aristotle.Physics.Typed.NaturalSelfMotionByAMoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutForced.model.ByNature) (TruthCore.Models.Physics.PhysicalWithoutForced.model.SelfMovedIn) (TruthCore.Models.Physics.PhysicalWithoutForced.model.MovesIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.NaturalSelfMotionByAMoverReading
  decide

theorem evaluation4 : @TruthCore.Greek.Aristotle.Physics.Typed.PassiveNaturalMotionByGeneratorOrRemoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutForced.model.PassiveNaturalIn) (TruthCore.Models.Physics.PhysicalWithoutForced.model.MovesIn) (TruthCore.Models.Physics.PhysicalWithoutForced.model.MovesPerAccidensIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.PassiveNaturalMotionByGeneratorOrRemoverReading
  decide

theorem evaluation5 : @TruthCore.Greek.Aristotle.Physics.Typed.PerAccidensMovedPassiveMotionHasPerSeMoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutForced.model.PassiveNaturalIn) (TruthCore.Models.Physics.PhysicalWithoutForced.model.MovesIn) (TruthCore.Models.Physics.PhysicalWithoutForced.model.MovesPerAccidensIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.PerAccidensMovedPassiveMotionHasPerSeMoverReading
  decide

theorem evaluation6 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.EveryPhysicalMotionHasAPerSeMoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutForced.model.IsPhysicalRespect) (TruthCore.Models.Physics.PhysicalWithoutForced.model.MovedIn) (TruthCore.Models.Physics.PhysicalWithoutForced.model.MovesIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryPhysicalMotionHasAPerSeMoverReading
  decide

theorem evaluation7 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.EveryMovedThingMovedPerSeOrPerAccidensReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutForced.model.IsPhysicalRespect) (TruthCore.Models.Physics.PhysicalWithoutForced.model.MovedIn) (TruthCore.Models.Physics.PhysicalWithoutForced.model.MovesIn) (TruthCore.Models.Physics.PhysicalWithoutForced.model.MovesPerAccidensIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryMovedThingMovedPerSeOrPerAccidensReading
  decide

end PhysicalWithoutForced
namespace PhysicalWithoutSelf
def model : Model where
  IsPhysicalRespect := fun _ => True
  MovedIn := fun _ _ => True
  ByNature := fun _ _ => True
  ByForce := fun _ _ => False
  SelfMovedIn := fun _ _ => True
  PassiveNaturalIn := fun _ _ => False
  InAct := fun _ _ => False
  InPotency := fun _ _ => False
  ActualizedQuaPotential := fun _ _ => False
  MovesIn := fun _ _ _ => False
  MovesPerAccidensIn := fun _ _ _ => False
theorem evaluation0 : @TruthCore.Greek.Aristotle.Physics.Typed.EveryMotionNaturalOrForcedReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.IsPhysicalRespect) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.MovedIn) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.ByNature) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.ByForce) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryMotionNaturalOrForcedReading
  decide

theorem evaluation1 : @TruthCore.Greek.Aristotle.Physics.Typed.NaturalMotionSelfOrPassiveReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.ByNature) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.SelfMovedIn) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.PassiveNaturalIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.NaturalMotionSelfOrPassiveReading
  decide

theorem evaluation2 : @TruthCore.Greek.Aristotle.Physics.Typed.ForcedMotionByAnotherReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.ByForce) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.MovesIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.ForcedMotionByAnotherReading
  decide

theorem evaluation3 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.NaturalSelfMotionByAMoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.ByNature) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.SelfMovedIn) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.MovesIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.NaturalSelfMotionByAMoverReading
  decide

theorem evaluation4 : @TruthCore.Greek.Aristotle.Physics.Typed.PassiveNaturalMotionByGeneratorOrRemoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.PassiveNaturalIn) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.MovesIn) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.MovesPerAccidensIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.PassiveNaturalMotionByGeneratorOrRemoverReading
  decide

theorem evaluation5 : @TruthCore.Greek.Aristotle.Physics.Typed.PerAccidensMovedPassiveMotionHasPerSeMoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.PassiveNaturalIn) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.MovesIn) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.MovesPerAccidensIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.PerAccidensMovedPassiveMotionHasPerSeMoverReading
  decide

theorem evaluation6 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.EveryPhysicalMotionHasAPerSeMoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.IsPhysicalRespect) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.MovedIn) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.MovesIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryPhysicalMotionHasAPerSeMoverReading
  decide

theorem evaluation7 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.EveryMovedThingMovedPerSeOrPerAccidensReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.IsPhysicalRespect) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.MovedIn) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.MovesIn) (TruthCore.Models.Physics.PhysicalWithoutSelf.model.MovesPerAccidensIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryMovedThingMovedPerSeOrPerAccidensReading
  decide

end PhysicalWithoutSelf
namespace PhysicalWithoutPassive
def model : Model where
  IsPhysicalRespect := fun _ => True
  MovedIn := fun _ _ => True
  ByNature := fun _ _ => True
  ByForce := fun _ _ => False
  SelfMovedIn := fun _ _ => False
  PassiveNaturalIn := fun _ _ => True
  InAct := fun _ _ => False
  InPotency := fun _ _ => False
  ActualizedQuaPotential := fun _ _ => False
  MovesIn := fun _ _ _ => False
  MovesPerAccidensIn := fun _ _ _ => False
theorem evaluation0 : @TruthCore.Greek.Aristotle.Physics.Typed.EveryMotionNaturalOrForcedReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.IsPhysicalRespect) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.MovedIn) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.ByNature) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.ByForce) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryMotionNaturalOrForcedReading
  decide

theorem evaluation1 : @TruthCore.Greek.Aristotle.Physics.Typed.NaturalMotionSelfOrPassiveReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.ByNature) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.SelfMovedIn) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.PassiveNaturalIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.NaturalMotionSelfOrPassiveReading
  decide

theorem evaluation2 : @TruthCore.Greek.Aristotle.Physics.Typed.ForcedMotionByAnotherReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.ByForce) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.MovesIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.ForcedMotionByAnotherReading
  decide

theorem evaluation3 : @TruthCore.Greek.Aristotle.Physics.Typed.NaturalSelfMotionByAMoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.ByNature) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.SelfMovedIn) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.MovesIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.NaturalSelfMotionByAMoverReading
  decide

theorem evaluation4 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.PassiveNaturalMotionByGeneratorOrRemoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.PassiveNaturalIn) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.MovesIn) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.MovesPerAccidensIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.PassiveNaturalMotionByGeneratorOrRemoverReading
  decide

theorem evaluation5 : @TruthCore.Greek.Aristotle.Physics.Typed.PerAccidensMovedPassiveMotionHasPerSeMoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.PassiveNaturalIn) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.MovesIn) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.MovesPerAccidensIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.PerAccidensMovedPassiveMotionHasPerSeMoverReading
  decide

theorem evaluation6 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.EveryPhysicalMotionHasAPerSeMoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.IsPhysicalRespect) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.MovedIn) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.MovesIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryPhysicalMotionHasAPerSeMoverReading
  decide

theorem evaluation7 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.EveryMovedThingMovedPerSeOrPerAccidensReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.IsPhysicalRespect) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.MovedIn) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.MovesIn) (TruthCore.Models.Physics.PhysicalWithoutPassive.model.MovesPerAccidensIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryMovedThingMovedPerSeOrPerAccidensReading
  decide

end PhysicalWithoutPassive
namespace PhysicalWithoutPerSeExtension
def model : Model where
  IsPhysicalRespect := fun _ => True
  MovedIn := fun _ _ => True
  ByNature := fun _ _ => True
  ByForce := fun _ _ => False
  SelfMovedIn := fun _ _ => False
  PassiveNaturalIn := fun _ _ => True
  InAct := fun _ _ => False
  InPotency := fun _ _ => False
  ActualizedQuaPotential := fun _ _ => False
  MovesIn := fun _ _ _ => False
  MovesPerAccidensIn := fun _ _ _ => True
theorem evaluation0 : @TruthCore.Greek.Aristotle.Physics.Typed.EveryMotionNaturalOrForcedReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.IsPhysicalRespect) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.MovedIn) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.ByNature) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.ByForce) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryMotionNaturalOrForcedReading
  decide

theorem evaluation1 : @TruthCore.Greek.Aristotle.Physics.Typed.NaturalMotionSelfOrPassiveReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.ByNature) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.SelfMovedIn) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.PassiveNaturalIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.NaturalMotionSelfOrPassiveReading
  decide

theorem evaluation2 : @TruthCore.Greek.Aristotle.Physics.Typed.ForcedMotionByAnotherReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.ByForce) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.MovesIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.ForcedMotionByAnotherReading
  decide

theorem evaluation3 : @TruthCore.Greek.Aristotle.Physics.Typed.NaturalSelfMotionByAMoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.ByNature) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.SelfMovedIn) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.MovesIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.NaturalSelfMotionByAMoverReading
  decide

theorem evaluation4 : @TruthCore.Greek.Aristotle.Physics.Typed.PassiveNaturalMotionByGeneratorOrRemoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.PassiveNaturalIn) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.MovesIn) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.MovesPerAccidensIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.PassiveNaturalMotionByGeneratorOrRemoverReading
  decide

theorem evaluation5 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.PerAccidensMovedPassiveMotionHasPerSeMoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.PassiveNaturalIn) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.MovesIn) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.MovesPerAccidensIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.PerAccidensMovedPassiveMotionHasPerSeMoverReading
  decide

theorem evaluation6 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.EveryPhysicalMotionHasAPerSeMoverReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.IsPhysicalRespect) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.MovedIn) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.MovesIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryPhysicalMotionHasAPerSeMoverReading
  decide

theorem evaluation7 : @TruthCore.Greek.Aristotle.Physics.Typed.EveryMovedThingMovedPerSeOrPerAccidensReading (Unit) (Unit) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.IsPhysicalRespect) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.MovedIn) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.MovesIn) (TruthCore.Models.Physics.PhysicalWithoutPerSeExtension.model.MovesPerAccidensIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryMovedThingMovedPerSeOrPerAccidensReading
  decide

end PhysicalWithoutPerSeExtension
namespace SelfMoverWithoutAnalysis
def model : Model where
  IsPhysicalRespect := fun _ => False
  MovedIn := fun _ _ => True
  ByNature := fun _ _ => False
  ByForce := fun _ _ => False
  SelfMovedIn := fun _ _ => False
  PassiveNaturalIn := fun _ _ => False
  InAct := fun _ _ => True
  InPotency := fun _ _ => False
  ActualizedQuaPotential := fun _ _ => False
  MovesIn := fun _ _ _ => True
  MovesPerAccidensIn := fun _ _ _ => False
theorem evaluation0 : ¬ (@TruthCore.Greek.Aristotle.Physics.BeingMovedIsActualizationOfPotencyReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutAnalysis.model.MovedIn) (TruthCore.Models.Physics.SelfMoverWithoutAnalysis.model.InPotency) (TruthCore.Models.Physics.SelfMoverWithoutAnalysis.model.ActualizedQuaPotential)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.BeingMovedIsActualizationOfPotencyReading
  decide

theorem evaluation1 : @TruthCore.Greek.Aristotle.Physics.Typed.MovingIsInTheMovedReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutAnalysis.model.MovesIn) (TruthCore.Models.Physics.SelfMoverWithoutAnalysis.model.MovedIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.MovingIsInTheMovedReading
  decide

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutAnalysis.model.MovesIn) (TruthCore.Models.Physics.SelfMoverWithoutAnalysis.model.InAct) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading
  decide

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutAnalysis.model.InAct) (TruthCore.Models.Physics.SelfMoverWithoutAnalysis.model.InPotency) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading
  decide

theorem evaluation4 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.NoMoverMovesItselfInItsRespectReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutAnalysis.model.MovesIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.NoMoverMovesItselfInItsRespectReading
  decide

end SelfMoverWithoutAnalysis
namespace SelfMoverWithoutInMoved
def model : Model where
  IsPhysicalRespect := fun _ => False
  MovedIn := fun _ _ => False
  ByNature := fun _ _ => False
  ByForce := fun _ _ => False
  SelfMovedIn := fun _ _ => False
  PassiveNaturalIn := fun _ _ => False
  InAct := fun _ _ => True
  InPotency := fun _ _ => False
  ActualizedQuaPotential := fun _ _ => False
  MovesIn := fun _ _ _ => True
  MovesPerAccidensIn := fun _ _ _ => False
theorem evaluation0 : @TruthCore.Greek.Aristotle.Physics.BeingMovedIsActualizationOfPotencyReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutInMoved.model.MovedIn) (TruthCore.Models.Physics.SelfMoverWithoutInMoved.model.InPotency) (TruthCore.Models.Physics.SelfMoverWithoutInMoved.model.ActualizedQuaPotential) := by
  unfold model TruthCore.Greek.Aristotle.Physics.BeingMovedIsActualizationOfPotencyReading
  decide

theorem evaluation1 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.MovingIsInTheMovedReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutInMoved.model.MovesIn) (TruthCore.Models.Physics.SelfMoverWithoutInMoved.model.MovedIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.MovingIsInTheMovedReading
  decide

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutInMoved.model.MovesIn) (TruthCore.Models.Physics.SelfMoverWithoutInMoved.model.InAct) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading
  decide

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutInMoved.model.InAct) (TruthCore.Models.Physics.SelfMoverWithoutInMoved.model.InPotency) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading
  decide

theorem evaluation4 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.NoMoverMovesItselfInItsRespectReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutInMoved.model.MovesIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.NoMoverMovesItselfInItsRespectReading
  decide

end SelfMoverWithoutInMoved
namespace SelfMoverWithoutInAct
def model : Model where
  IsPhysicalRespect := fun _ => False
  MovedIn := fun _ _ => True
  ByNature := fun _ _ => False
  ByForce := fun _ _ => False
  SelfMovedIn := fun _ _ => False
  PassiveNaturalIn := fun _ _ => False
  InAct := fun _ _ => False
  InPotency := fun _ _ => True
  ActualizedQuaPotential := fun _ _ => True
  MovesIn := fun _ _ _ => True
  MovesPerAccidensIn := fun _ _ _ => False
theorem evaluation0 : @TruthCore.Greek.Aristotle.Physics.BeingMovedIsActualizationOfPotencyReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutInAct.model.MovedIn) (TruthCore.Models.Physics.SelfMoverWithoutInAct.model.InPotency) (TruthCore.Models.Physics.SelfMoverWithoutInAct.model.ActualizedQuaPotential) := by
  unfold model TruthCore.Greek.Aristotle.Physics.BeingMovedIsActualizationOfPotencyReading
  decide

theorem evaluation1 : @TruthCore.Greek.Aristotle.Physics.Typed.MovingIsInTheMovedReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutInAct.model.MovesIn) (TruthCore.Models.Physics.SelfMoverWithoutInAct.model.MovedIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.MovingIsInTheMovedReading
  decide

theorem evaluation2 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutInAct.model.MovesIn) (TruthCore.Models.Physics.SelfMoverWithoutInAct.model.InAct)) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading
  decide

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutInAct.model.InAct) (TruthCore.Models.Physics.SelfMoverWithoutInAct.model.InPotency) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading
  decide

theorem evaluation4 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.NoMoverMovesItselfInItsRespectReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutInAct.model.MovesIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.NoMoverMovesItselfInItsRespectReading
  decide

end SelfMoverWithoutInAct
namespace SelfMoverWithoutNotBoth
def model : Model where
  IsPhysicalRespect := fun _ => False
  MovedIn := fun _ _ => True
  ByNature := fun _ _ => False
  ByForce := fun _ _ => False
  SelfMovedIn := fun _ _ => False
  PassiveNaturalIn := fun _ _ => False
  InAct := fun _ _ => True
  InPotency := fun _ _ => True
  ActualizedQuaPotential := fun _ _ => True
  MovesIn := fun _ _ _ => True
  MovesPerAccidensIn := fun _ _ _ => False
theorem evaluation0 : @TruthCore.Greek.Aristotle.Physics.BeingMovedIsActualizationOfPotencyReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutNotBoth.model.MovedIn) (TruthCore.Models.Physics.SelfMoverWithoutNotBoth.model.InPotency) (TruthCore.Models.Physics.SelfMoverWithoutNotBoth.model.ActualizedQuaPotential) := by
  unfold model TruthCore.Greek.Aristotle.Physics.BeingMovedIsActualizationOfPotencyReading
  decide

theorem evaluation1 : @TruthCore.Greek.Aristotle.Physics.Typed.MovingIsInTheMovedReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutNotBoth.model.MovesIn) (TruthCore.Models.Physics.SelfMoverWithoutNotBoth.model.MovedIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.MovingIsInTheMovedReading
  decide

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutNotBoth.model.MovesIn) (TruthCore.Models.Physics.SelfMoverWithoutNotBoth.model.InAct) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading
  decide

theorem evaluation3 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutNotBoth.model.InAct) (TruthCore.Models.Physics.SelfMoverWithoutNotBoth.model.InPotency)) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading
  decide

theorem evaluation4 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.NoMoverMovesItselfInItsRespectReading (Unit) (Unit) (TruthCore.Models.Physics.SelfMoverWithoutNotBoth.model.MovesIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.NoMoverMovesItselfInItsRespectReading
  decide

end SelfMoverWithoutNotBoth
namespace ScopeWithoutPhysicalScope
def model : Model where
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
theorem evaluation0 : @TruthCore.Greek.Aristotle.Physics.Typed.EveryPhysicalMotionHasAPerSeMoverReading (Unit) (Unit) (TruthCore.Models.Physics.ScopeWithoutPhysicalScope.model.IsPhysicalRespect) (TruthCore.Models.Physics.ScopeWithoutPhysicalScope.model.MovedIn) (TruthCore.Models.Physics.ScopeWithoutPhysicalScope.model.MovesIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryPhysicalMotionHasAPerSeMoverReading
  decide

theorem evaluation1 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.EveryReductionIsPhysicalMotionReading (Unit) (Unit) (TruthCore.Models.Physics.ScopeWithoutPhysicalScope.model.IsPhysicalRespect) (TruthCore.Models.Physics.ScopeWithoutPhysicalScope.model.MovedIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryReductionIsPhysicalMotionReading
  decide

theorem evaluation2 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading (Unit) (Unit) (TruthCore.Models.Physics.ScopeWithoutPhysicalScope.model.MovedIn) (TruthCore.Models.Physics.ScopeWithoutPhysicalScope.model.MovesIn)) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading
  decide

end ScopeWithoutPhysicalScope
namespace ScopeWithoutMover
def model : Model where
  IsPhysicalRespect := fun _ => True
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
theorem evaluation0 : ¬ (@TruthCore.Greek.Aristotle.Physics.Typed.EveryPhysicalMotionHasAPerSeMoverReading (Unit) (Unit) (TruthCore.Models.Physics.ScopeWithoutMover.model.IsPhysicalRespect) (TruthCore.Models.Physics.ScopeWithoutMover.model.MovedIn) (TruthCore.Models.Physics.ScopeWithoutMover.model.MovesIn)) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryPhysicalMotionHasAPerSeMoverReading
  decide

theorem evaluation1 : @TruthCore.Greek.Aristotle.Physics.Typed.EveryReductionIsPhysicalMotionReading (Unit) (Unit) (TruthCore.Models.Physics.ScopeWithoutMover.model.IsPhysicalRespect) (TruthCore.Models.Physics.ScopeWithoutMover.model.MovedIn) := by
  unfold model TruthCore.Greek.Aristotle.Physics.Typed.EveryReductionIsPhysicalMotionReading
  decide

theorem evaluation2 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading (Unit) (Unit) (TruthCore.Models.Physics.ScopeWithoutMover.model.MovedIn) (TruthCore.Models.Physics.ScopeWithoutMover.model.MovesIn)) := by
  unfold model TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading
  decide

end ScopeWithoutMover
end TruthCore.Models.Physics
