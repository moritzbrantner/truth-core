import TruthCore.Greek.Aristotle.Physics.Typed.Motion
namespace TruthCore.Results.Aristotle.Physics.Typed.EveryPhysicalMotionHasAPerSeMover
open TruthCore.Greek.Aristotle.Physics.Typed

/-- Every physical motion has a per se mover in its respect, from *Physics* VIII.4's
division (255b31-256a3) read literally, together with the added, unattributed
premise that a light or heavy thing's natural motion that has a per accidens mover
also has a per se mover. A forced motion has another as mover; a natural
self-motion has a mover; the natural motion of the light and the heavy has a per
se mover outright, or a per accidens mover and then, by the added premise, a per
se mover as well. -/
theorem everyPhysicalMotionHasAPerSeMover {Being : Type} {Respect : Type}
    (IsPhysicalRespect : Respect → Prop)
    (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
    (MovesIn MovesPerAccidensIn : Being → Being → Respect → Prop)
    (hDivision : EveryMotionNaturalOrForcedReading IsPhysicalRespect MovedIn ByNature ByForce)
    (hNatural : NaturalMotionSelfOrPassiveReading ByNature SelfMovedIn PassiveNaturalIn)
    (hForced : ForcedMotionByAnotherReading ByForce MovesIn)
    (hSelf : NaturalSelfMotionByAMoverReading ByNature SelfMovedIn MovesIn)
    (hPassive : PassiveNaturalMotionByGeneratorOrRemoverReading PassiveNaturalIn MovesIn
      MovesPerAccidensIn)
    (hPerSe : PerAccidensMovedPassiveMotionHasPerSeMoverReading PassiveNaturalIn MovesIn
      MovesPerAccidensIn) :
    EveryPhysicalMotionHasAPerSeMoverReading IsPhysicalRespect MovedIn MovesIn := by
  sorry

/-- Each of the six premises is needed. In each model one thing is moved in one
physical respect, every remaining premise holds, and nothing moves it per se. -/
theorem premisesNeeded :
    (¬ ∀ (Being Respect : Type) (IsPhysicalRespect : Respect → Prop)
        (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
        (MovesIn MovesPerAccidensIn : Being → Being → Respect → Prop),
      NaturalMotionSelfOrPassiveReading ByNature SelfMovedIn PassiveNaturalIn →
      ForcedMotionByAnotherReading ByForce MovesIn →
      NaturalSelfMotionByAMoverReading ByNature SelfMovedIn MovesIn →
      PassiveNaturalMotionByGeneratorOrRemoverReading PassiveNaturalIn MovesIn
        MovesPerAccidensIn →
      PerAccidensMovedPassiveMotionHasPerSeMoverReading PassiveNaturalIn MovesIn
        MovesPerAccidensIn →
      EveryPhysicalMotionHasAPerSeMoverReading IsPhysicalRespect MovedIn MovesIn) ∧
    (¬ ∀ (Being Respect : Type) (IsPhysicalRespect : Respect → Prop)
        (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
        (MovesIn MovesPerAccidensIn : Being → Being → Respect → Prop),
      EveryMotionNaturalOrForcedReading IsPhysicalRespect MovedIn ByNature ByForce →
      ForcedMotionByAnotherReading ByForce MovesIn →
      NaturalSelfMotionByAMoverReading ByNature SelfMovedIn MovesIn →
      PassiveNaturalMotionByGeneratorOrRemoverReading PassiveNaturalIn MovesIn
        MovesPerAccidensIn →
      PerAccidensMovedPassiveMotionHasPerSeMoverReading PassiveNaturalIn MovesIn
        MovesPerAccidensIn →
      EveryPhysicalMotionHasAPerSeMoverReading IsPhysicalRespect MovedIn MovesIn) ∧
    (¬ ∀ (Being Respect : Type) (IsPhysicalRespect : Respect → Prop)
        (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
        (MovesIn MovesPerAccidensIn : Being → Being → Respect → Prop),
      EveryMotionNaturalOrForcedReading IsPhysicalRespect MovedIn ByNature ByForce →
      NaturalMotionSelfOrPassiveReading ByNature SelfMovedIn PassiveNaturalIn →
      NaturalSelfMotionByAMoverReading ByNature SelfMovedIn MovesIn →
      PassiveNaturalMotionByGeneratorOrRemoverReading PassiveNaturalIn MovesIn
        MovesPerAccidensIn →
      PerAccidensMovedPassiveMotionHasPerSeMoverReading PassiveNaturalIn MovesIn
        MovesPerAccidensIn →
      EveryPhysicalMotionHasAPerSeMoverReading IsPhysicalRespect MovedIn MovesIn) ∧
    (¬ ∀ (Being Respect : Type) (IsPhysicalRespect : Respect → Prop)
        (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
        (MovesIn MovesPerAccidensIn : Being → Being → Respect → Prop),
      EveryMotionNaturalOrForcedReading IsPhysicalRespect MovedIn ByNature ByForce →
      NaturalMotionSelfOrPassiveReading ByNature SelfMovedIn PassiveNaturalIn →
      ForcedMotionByAnotherReading ByForce MovesIn →
      PassiveNaturalMotionByGeneratorOrRemoverReading PassiveNaturalIn MovesIn
        MovesPerAccidensIn →
      PerAccidensMovedPassiveMotionHasPerSeMoverReading PassiveNaturalIn MovesIn
        MovesPerAccidensIn →
      EveryPhysicalMotionHasAPerSeMoverReading IsPhysicalRespect MovedIn MovesIn) ∧
    (¬ ∀ (Being Respect : Type) (IsPhysicalRespect : Respect → Prop)
        (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
        (MovesIn MovesPerAccidensIn : Being → Being → Respect → Prop),
      EveryMotionNaturalOrForcedReading IsPhysicalRespect MovedIn ByNature ByForce →
      NaturalMotionSelfOrPassiveReading ByNature SelfMovedIn PassiveNaturalIn →
      ForcedMotionByAnotherReading ByForce MovesIn →
      NaturalSelfMotionByAMoverReading ByNature SelfMovedIn MovesIn →
      PerAccidensMovedPassiveMotionHasPerSeMoverReading PassiveNaturalIn MovesIn
        MovesPerAccidensIn →
      EveryPhysicalMotionHasAPerSeMoverReading IsPhysicalRespect MovedIn MovesIn) ∧
    (¬ ∀ (Being Respect : Type) (IsPhysicalRespect : Respect → Prop)
        (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
        (MovesIn MovesPerAccidensIn : Being → Being → Respect → Prop),
      EveryMotionNaturalOrForcedReading IsPhysicalRespect MovedIn ByNature ByForce →
      NaturalMotionSelfOrPassiveReading ByNature SelfMovedIn PassiveNaturalIn →
      ForcedMotionByAnotherReading ByForce MovesIn →
      NaturalSelfMotionByAMoverReading ByNature SelfMovedIn MovesIn →
      PassiveNaturalMotionByGeneratorOrRemoverReading PassiveNaturalIn MovesIn
        MovesPerAccidensIn →
      EveryPhysicalMotionHasAPerSeMoverReading IsPhysicalRespect MovedIn MovesIn) := by
  sorry

end TruthCore.Results.Aristotle.Physics.Typed.EveryPhysicalMotionHasAPerSeMover
