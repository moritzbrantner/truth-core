import TruthCore.Greek.Aristotle.Physics.Typed.Motion
namespace TruthCore.Results.Aristotle.Physics.Typed.EveryMovedPerSeOrPerAccidens
open TruthCore.Greek.Aristotle.Physics.Typed
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- *Physics* VIII.4's closing argument (255b31-256a3), on the literal reading of
its last step: every motion is natural or forced; a forced motion has another as
mover; a natural motion is either a self-motion, which has a mover, or the motion
of something light or heavy, which is moved by its generator or, per accidens, by
the remover of a hindrance. So every moved thing is moved by something, per se or
per accidens. -/
theorem everyMovedPerSeOrPerAccidens {Being : Type} {Respect : Type}
    (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
    (MovesIn MovesPerAccidensIn : Being → Being → Respect → Prop)
    (hDivision : EveryMotionNaturalOrForcedReading MovedIn ByNature ByForce)
    (hNatural : NaturalMotionSelfOrPassiveReading ByNature SelfMovedIn PassiveNaturalIn)
    (hForced : ForcedMotionByAnotherReading ByForce MovesIn)
    (hSelf : NaturalSelfMotionByAMoverReading ByNature SelfMovedIn MovesIn)
    (hPassive : PassiveNaturalMotionByGeneratorOrRemoverReading PassiveNaturalIn MovesIn
      MovesPerAccidensIn) :
    EveryMovedThingMovedPerSeOrPerAccidensReading MovedIn MovesIn MovesPerAccidensIn := by
  sorry

/-- Each of the five premises is needed. In each model one thing is moved in one
respect, every remaining premise holds, and nothing moves it in any way. -/
theorem premisesNeeded :
    (¬ ∀ (Being Respect : Type)
        (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
        (MovesIn MovesPerAccidensIn : Being → Being → Respect → Prop),
      NaturalMotionSelfOrPassiveReading ByNature SelfMovedIn PassiveNaturalIn →
      ForcedMotionByAnotherReading ByForce MovesIn →
      NaturalSelfMotionByAMoverReading ByNature SelfMovedIn MovesIn →
      PassiveNaturalMotionByGeneratorOrRemoverReading PassiveNaturalIn MovesIn
        MovesPerAccidensIn →
      EveryMovedThingMovedPerSeOrPerAccidensReading MovedIn MovesIn MovesPerAccidensIn) ∧
    (¬ ∀ (Being Respect : Type)
        (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
        (MovesIn MovesPerAccidensIn : Being → Being → Respect → Prop),
      EveryMotionNaturalOrForcedReading MovedIn ByNature ByForce →
      ForcedMotionByAnotherReading ByForce MovesIn →
      NaturalSelfMotionByAMoverReading ByNature SelfMovedIn MovesIn →
      PassiveNaturalMotionByGeneratorOrRemoverReading PassiveNaturalIn MovesIn
        MovesPerAccidensIn →
      EveryMovedThingMovedPerSeOrPerAccidensReading MovedIn MovesIn MovesPerAccidensIn) ∧
    (¬ ∀ (Being Respect : Type)
        (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
        (MovesIn MovesPerAccidensIn : Being → Being → Respect → Prop),
      EveryMotionNaturalOrForcedReading MovedIn ByNature ByForce →
      NaturalMotionSelfOrPassiveReading ByNature SelfMovedIn PassiveNaturalIn →
      NaturalSelfMotionByAMoverReading ByNature SelfMovedIn MovesIn →
      PassiveNaturalMotionByGeneratorOrRemoverReading PassiveNaturalIn MovesIn
        MovesPerAccidensIn →
      EveryMovedThingMovedPerSeOrPerAccidensReading MovedIn MovesIn MovesPerAccidensIn) ∧
    (¬ ∀ (Being Respect : Type)
        (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
        (MovesIn MovesPerAccidensIn : Being → Being → Respect → Prop),
      EveryMotionNaturalOrForcedReading MovedIn ByNature ByForce →
      NaturalMotionSelfOrPassiveReading ByNature SelfMovedIn PassiveNaturalIn →
      ForcedMotionByAnotherReading ByForce MovesIn →
      PassiveNaturalMotionByGeneratorOrRemoverReading PassiveNaturalIn MovesIn
        MovesPerAccidensIn →
      EveryMovedThingMovedPerSeOrPerAccidensReading MovedIn MovesIn MovesPerAccidensIn) ∧
    (¬ ∀ (Being Respect : Type)
        (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
        (MovesIn MovesPerAccidensIn : Being → Being → Respect → Prop),
      EveryMotionNaturalOrForcedReading MovedIn ByNature ByForce →
      NaturalMotionSelfOrPassiveReading ByNature SelfMovedIn PassiveNaturalIn →
      ForcedMotionByAnotherReading ByForce MovesIn →
      NaturalSelfMotionByAMoverReading ByNature SelfMovedIn MovesIn →
      EveryMovedThingMovedPerSeOrPerAccidensReading MovedIn MovesIn MovesPerAccidensIn) := by
  sorry

/-- The literal reading does not give the *prima via*'s premise that whatever is
moved in a respect has a mover in that respect: a light thing moved only by the
remover of a hindrance satisfies every premise and has no per se mover. -/
theorem literalReadingDoesNotGivePerSeMover :
    ¬ ∀ (Being Respect : Type)
        (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
        (MovesIn MovesPerAccidensIn : Being → Being → Respect → Prop),
      EveryMotionNaturalOrForcedReading MovedIn ByNature ByForce →
      NaturalMotionSelfOrPassiveReading ByNature SelfMovedIn PassiveNaturalIn →
      ForcedMotionByAnotherReading ByForce MovesIn →
      NaturalSelfMotionByAMoverReading ByNature SelfMovedIn MovesIn →
      PassiveNaturalMotionByGeneratorOrRemoverReading PassiveNaturalIn MovesIn
        MovesPerAccidensIn →
      ReducedOnlyByAMoverReading MovedIn MovesIn := by
  sorry

end TruthCore.Results.Aristotle.Physics.Typed.EveryMovedPerSeOrPerAccidens
