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
  -- INF-ARIST-PHYS-VIII-4-EVERY-MOVED-PER-SE-OR-PER-ACCIDENS
  intro x r hMoved
  rcases hDivision x r hMoved with hNat | hForce
  · rcases hNatural x r hNat with hSelfMoved | hPas
    · obtain ⟨y, hy⟩ := hSelf x r hNat hSelfMoved
      exact ⟨y, Or.inl hy⟩
    · exact hPassive x r hPas
  · obtain ⟨y, _, hy⟩ := hForced x r hForce
    exact ⟨y, Or.inl hy⟩

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
  have noMover : ∀ (P : Unit → Unit → Unit → Prop),
      (∀ y z r, ¬ P y z r) → ¬ (∃ y, P y () () ∨ False) := by
    intro P hP ⟨y, hy⟩
    rcases hy with hy | hy
    · exact hP y () () hy
    · exact hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- without the natural/forced division: a motion of neither kind
    intro h
    exact noMover (fun _ _ _ => False) (fun _ _ _ hf => hf)
      (h Unit Unit (fun _ _ => True) (fun _ _ => False) (fun _ _ => False)
        (fun _ _ => False) (fun _ _ => False) (fun _ _ _ => False) (fun _ _ _ => False)
        (fun _ _ hn => hn.elim) (fun _ _ hf => hf.elim) (fun _ _ hn => hn.elim)
        (fun _ _ hp => hp.elim) () () trivial)
  · -- without the division of natural motion: a natural motion of neither kind
    intro h
    exact noMover (fun _ _ _ => False) (fun _ _ _ hf => hf)
      (h Unit Unit (fun _ _ => True) (fun _ _ => True) (fun _ _ => False)
        (fun _ _ => False) (fun _ _ => False) (fun _ _ _ => False) (fun _ _ _ => False)
        (fun _ _ _ => Or.inl trivial) (fun _ _ hf => hf.elim) (fun _ _ _ hs => hs.elim)
        (fun _ _ hp => hp.elim) () () trivial)
  · -- without forced motion's mover: a forced motion with no mover
    intro h
    exact noMover (fun _ _ _ => False) (fun _ _ _ hf => hf)
      (h Unit Unit (fun _ _ => True) (fun _ _ => False) (fun _ _ => True)
        (fun _ _ => False) (fun _ _ => False) (fun _ _ _ => False) (fun _ _ _ => False)
        (fun _ _ _ => Or.inr trivial) (fun _ _ hn => hn.elim) (fun _ _ _ hs => hs.elim)
        (fun _ _ hp => hp.elim) () () trivial)
  · -- without self-motion's mover: a natural self-motion with no mover
    intro h
    exact noMover (fun _ _ _ => False) (fun _ _ _ hf => hf)
      (h Unit Unit (fun _ _ => True) (fun _ _ => True) (fun _ _ => False)
        (fun _ _ => True) (fun _ _ => False) (fun _ _ _ => False) (fun _ _ _ => False)
        (fun _ _ _ => Or.inl trivial) (fun _ _ _ => Or.inl trivial)
        (fun _ _ hf => hf.elim) (fun _ _ hp => hp.elim) () () trivial)
  · -- without the light and heavy's mover: such a motion with no mover
    intro h
    exact noMover (fun _ _ _ => False) (fun _ _ _ hf => hf)
      (h Unit Unit (fun _ _ => True) (fun _ _ => True) (fun _ _ => False)
        (fun _ _ => False) (fun _ _ => True) (fun _ _ _ => False) (fun _ _ _ => False)
        (fun _ _ _ => Or.inl trivial) (fun _ _ _ => Or.inr trivial)
        (fun _ _ hf => hf.elim) (fun _ _ _ hs => hs.elim) () () trivial)

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
  intro h
  obtain ⟨_, hy⟩ := h Unit Unit (fun _ _ => True) (fun _ _ => True) (fun _ _ => False)
    (fun _ _ => False) (fun _ _ => True) (fun _ _ _ => False) (fun _ _ _ => True)
    (fun _ _ _ => Or.inl trivial) (fun _ _ _ => Or.inr trivial)
    (fun _ _ hf => hf.elim) (fun _ _ _ hs => hs.elim)
    (fun _ _ _ => ⟨(), Or.inr trivial⟩) () () trivial
  exact hy

end TruthCore.Results.Aristotle.Physics.Typed.EveryMovedPerSeOrPerAccidens
