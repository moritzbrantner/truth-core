import TruthCore.Greek.Aristotle.Physics.Typed.Motion
namespace TruthCore.Results.Aristotle.Physics.Typed.EveryMovedHasAPerSeMover
open TruthCore.Greek.Aristotle.Physics.Typed
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- The *prima via*'s premise that whatever is moved in a respect is moved by
something in that respect, derived from *Physics* VIII.4's closing division
(255b31-256a3) with the generator reading of its last step: a forced motion has
another as mover; a natural self-motion has a mover; the natural motion of the
light and the heavy is moved per se by what generated it. -/
theorem everyMovedHasAPerSeMover {Being : Type} {Respect : Type}
    (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (hDivision : EveryMotionNaturalOrForcedReading MovedIn ByNature ByForce)
    (hNatural : NaturalMotionSelfOrPassiveReading ByNature SelfMovedIn PassiveNaturalIn)
    (hForced : ForcedMotionByAnotherReading ByForce MovesIn)
    (hSelf : NaturalSelfMotionByAMoverReading ByNature SelfMovedIn MovesIn)
    (hGenerator : PassiveNaturalMotionByGeneratorReading PassiveNaturalIn MovesIn) :
    ReducedOnlyByAMoverReading MovedIn MovesIn := by
  -- INF-ARIST-PHYS-VIII-4-EVERY-MOVED-HAS-A-PER-SE-MOVER
  intro x r hMoved
  rcases hDivision x r hMoved with hNat | hForce
  · rcases hNatural x r hNat with hSelfMoved | hPas
    · exact hSelf x r hNat hSelfMoved
    · exact hGenerator x r hPas
  · obtain ⟨y, _, hy⟩ := hForced x r hForce
    exact ⟨y, hy⟩

/-- Each of the five premises is needed. In each model one thing is moved in one
respect, every remaining premise holds, and nothing moves it. -/
theorem premisesNeeded :
    (¬ ∀ (Being Respect : Type)
        (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop),
      NaturalMotionSelfOrPassiveReading ByNature SelfMovedIn PassiveNaturalIn →
      ForcedMotionByAnotherReading ByForce MovesIn →
      NaturalSelfMotionByAMoverReading ByNature SelfMovedIn MovesIn →
      PassiveNaturalMotionByGeneratorReading PassiveNaturalIn MovesIn →
      ReducedOnlyByAMoverReading MovedIn MovesIn) ∧
    (¬ ∀ (Being Respect : Type)
        (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop),
      EveryMotionNaturalOrForcedReading MovedIn ByNature ByForce →
      ForcedMotionByAnotherReading ByForce MovesIn →
      NaturalSelfMotionByAMoverReading ByNature SelfMovedIn MovesIn →
      PassiveNaturalMotionByGeneratorReading PassiveNaturalIn MovesIn →
      ReducedOnlyByAMoverReading MovedIn MovesIn) ∧
    (¬ ∀ (Being Respect : Type)
        (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop),
      EveryMotionNaturalOrForcedReading MovedIn ByNature ByForce →
      NaturalMotionSelfOrPassiveReading ByNature SelfMovedIn PassiveNaturalIn →
      NaturalSelfMotionByAMoverReading ByNature SelfMovedIn MovesIn →
      PassiveNaturalMotionByGeneratorReading PassiveNaturalIn MovesIn →
      ReducedOnlyByAMoverReading MovedIn MovesIn) ∧
    (¬ ∀ (Being Respect : Type)
        (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop),
      EveryMotionNaturalOrForcedReading MovedIn ByNature ByForce →
      NaturalMotionSelfOrPassiveReading ByNature SelfMovedIn PassiveNaturalIn →
      ForcedMotionByAnotherReading ByForce MovesIn →
      PassiveNaturalMotionByGeneratorReading PassiveNaturalIn MovesIn →
      ReducedOnlyByAMoverReading MovedIn MovesIn) ∧
    (¬ ∀ (Being Respect : Type)
        (MovedIn ByNature ByForce SelfMovedIn PassiveNaturalIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop),
      EveryMotionNaturalOrForcedReading MovedIn ByNature ByForce →
      NaturalMotionSelfOrPassiveReading ByNature SelfMovedIn PassiveNaturalIn →
      ForcedMotionByAnotherReading ByForce MovesIn →
      NaturalSelfMotionByAMoverReading ByNature SelfMovedIn MovesIn →
      ReducedOnlyByAMoverReading MovedIn MovesIn) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- without the natural/forced division
    intro h
    obtain ⟨_, hy⟩ := h Unit Unit (fun _ _ => True) (fun _ _ => False) (fun _ _ => False)
      (fun _ _ => False) (fun _ _ => False) (fun _ _ _ => False)
      (fun _ _ hn => hn.elim) (fun _ _ hf => hf.elim) (fun _ _ hn => hn.elim)
      (fun _ _ hp => hp.elim) () () trivial
    exact hy
  · -- without the division of natural motion
    intro h
    obtain ⟨_, hy⟩ := h Unit Unit (fun _ _ => True) (fun _ _ => True) (fun _ _ => False)
      (fun _ _ => False) (fun _ _ => False) (fun _ _ _ => False)
      (fun _ _ _ => Or.inl trivial) (fun _ _ hf => hf.elim) (fun _ _ _ hs => hs.elim)
      (fun _ _ hp => hp.elim) () () trivial
    exact hy
  · -- without forced motion's mover
    intro h
    obtain ⟨_, hy⟩ := h Unit Unit (fun _ _ => True) (fun _ _ => False) (fun _ _ => True)
      (fun _ _ => False) (fun _ _ => False) (fun _ _ _ => False)
      (fun _ _ _ => Or.inr trivial) (fun _ _ hn => hn.elim) (fun _ _ _ hs => hs.elim)
      (fun _ _ hp => hp.elim) () () trivial
    exact hy
  · -- without self-motion's mover
    intro h
    obtain ⟨_, hy⟩ := h Unit Unit (fun _ _ => True) (fun _ _ => True) (fun _ _ => False)
      (fun _ _ => True) (fun _ _ => False) (fun _ _ _ => False)
      (fun _ _ _ => Or.inl trivial) (fun _ _ _ => Or.inl trivial)
      (fun _ _ hf => hf.elim) (fun _ _ hp => hp.elim) () () trivial
    exact hy
  · -- without the generator
    intro h
    obtain ⟨_, hy⟩ := h Unit Unit (fun _ _ => True) (fun _ _ => True) (fun _ _ => False)
      (fun _ _ => False) (fun _ _ => True) (fun _ _ _ => False)
      (fun _ _ _ => Or.inl trivial) (fun _ _ _ => Or.inr trivial)
      (fun _ _ hf => hf.elim) (fun _ _ _ hs => hs.elim) () () trivial
    exact hy

end TruthCore.Results.Aristotle.Physics.Typed.EveryMovedHasAPerSeMover
