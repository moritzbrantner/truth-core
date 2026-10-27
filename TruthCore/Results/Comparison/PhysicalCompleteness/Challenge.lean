import TruthCore.Alternatives.PhysicalCompleteness
import TruthCore.Greek.Aristotle.Physics.Typed.Motion
import TruthCore.Modern.Papineau.RiseOfPhysicalism
namespace TruthCore.Results.Comparison.PhysicalCompleteness
open TruthCore.Alternatives.PhysicalCompleteness
open TruthCore.Greek.Aristotle.Physics.Typed
open TruthCore.Modern.Papineau.RiseOfPhysicalism

/-- Papineau's completeness of physics, with two unattributed bridges, gives the
restricted mover premise STMT-EVERY-PHYSICAL-MOTION-HAS-A-PER-SE-MOVER: whatever
is moved in a respect of physical motion has a mover in that respect.

Transcription (single application): the proof applies the mover bridge, whose
consequent is the conclusion. Its content is the two open bridges; Papineau's
thesis supplies only the antecedent of the second. -/
theorem everyPhysicalMotionHasAMoverFromCompleteness
    {Being Respect Occurrence : Type}
    (IsPhysicalRespect : Respect → Prop)
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (motionOf : Being → Respect → Occurrence)
    (Physical IsEffect : Occurrence → Prop)
    (Prior : Occurrence → Occurrence → Prop)
    (FullyDeterminedByLaw : (Occurrence → Prop) → Occurrence → Prop)
    (hComplete : CompletenessOfPhysicsReading Physical IsEffect Prior FullyDeterminedByLaw)
    (hEffect : PhysicalMotionIsPhysicalEffect IsPhysicalRespect MovedIn motionOf Physical IsEffect)
    (hMover : PriorPhysicalDeterminationGivesMover MovedIn MovesIn motionOf Physical Prior
      FullyDeterminedByLaw) :
    EveryPhysicalMotionHasAPerSeMoverReading IsPhysicalRespect MovedIn MovesIn := by
  sorry

/-- Each of the three premises is needed: dropping any one, the other two hold
in a one-being, one-respect model where the moved thing has no mover. -/
theorem premisesNeeded :
    (¬ ∀ (Being Respect Occurrence : Type) (IsPhysicalRespect : Respect → Prop)
        (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
        (motionOf : Being → Respect → Occurrence) (Physical IsEffect : Occurrence → Prop)
        (Prior : Occurrence → Occurrence → Prop)
        (FullyDeterminedByLaw : (Occurrence → Prop) → Occurrence → Prop),
      PhysicalMotionIsPhysicalEffect IsPhysicalRespect MovedIn motionOf Physical IsEffect →
      PriorPhysicalDeterminationGivesMover MovedIn MovesIn motionOf Physical Prior
        FullyDeterminedByLaw →
      EveryPhysicalMotionHasAPerSeMoverReading IsPhysicalRespect MovedIn MovesIn) ∧
    (¬ ∀ (Being Respect Occurrence : Type) (IsPhysicalRespect : Respect → Prop)
        (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
        (motionOf : Being → Respect → Occurrence) (Physical IsEffect : Occurrence → Prop)
        (Prior : Occurrence → Occurrence → Prop)
        (FullyDeterminedByLaw : (Occurrence → Prop) → Occurrence → Prop),
      CompletenessOfPhysicsReading Physical IsEffect Prior FullyDeterminedByLaw →
      PriorPhysicalDeterminationGivesMover MovedIn MovesIn motionOf Physical Prior
        FullyDeterminedByLaw →
      EveryPhysicalMotionHasAPerSeMoverReading IsPhysicalRespect MovedIn MovesIn) ∧
    (¬ ∀ (Being Respect Occurrence : Type) (IsPhysicalRespect : Respect → Prop)
        (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
        (motionOf : Being → Respect → Occurrence) (Physical IsEffect : Occurrence → Prop)
        (Prior : Occurrence → Occurrence → Prop)
        (FullyDeterminedByLaw : (Occurrence → Prop) → Occurrence → Prop),
      CompletenessOfPhysicsReading Physical IsEffect Prior FullyDeterminedByLaw →
      PhysicalMotionIsPhysicalEffect IsPhysicalRespect MovedIn motionOf Physical IsEffect →
      EveryPhysicalMotionHasAPerSeMoverReading IsPhysicalRespect MovedIn MovesIn) := by
  sorry

end TruthCore.Results.Comparison.PhysicalCompleteness
