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
  -- INF-ARIST-PHYS-VIII-4-EVERY-PHYSICAL-MOTION-HAS-A-PER-SE-MOVER
  intro x r hPhys hMoved
  rcases hDivision x r hPhys hMoved with hNat | hForce
  · rcases hNatural x r hNat with hSelfMoved | hPas
    · exact hSelf x r hNat hSelfMoved
    · obtain ⟨y, hy | hy⟩ := hPassive x r hPas
      · exact ⟨y, hy⟩
      · exact hPerSe x r y hPas hy
  · obtain ⟨y, _, hy⟩ := hForced x r hForce
    exact ⟨y, hy⟩

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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- without the natural/forced division
    intro h
    obtain ⟨_, hy⟩ := h Unit Unit (fun _ => True) (fun _ _ => True) (fun _ _ => False)
      (fun _ _ => False) (fun _ _ => False) (fun _ _ => False) (fun _ _ _ => False)
      (fun _ _ _ => False)
      (fun _ _ hn => hn.elim) (fun _ _ hf => hf.elim) (fun _ _ hn => hn.elim)
      (fun _ _ hp => hp.elim) (fun _ _ _ hp => hp.elim) () () trivial trivial
    exact hy
  · -- without the division of natural motion
    intro h
    obtain ⟨_, hy⟩ := h Unit Unit (fun _ => True) (fun _ _ => True) (fun _ _ => True)
      (fun _ _ => False) (fun _ _ => False) (fun _ _ => False) (fun _ _ _ => False)
      (fun _ _ _ => False)
      (fun _ _ _ _ => Or.inl trivial) (fun _ _ hf => hf.elim) (fun _ _ _ hs => hs.elim)
      (fun _ _ hp => hp.elim) (fun _ _ _ hp => hp.elim) () () trivial trivial
    exact hy
  · -- without forced motion's mover
    intro h
    obtain ⟨_, hy⟩ := h Unit Unit (fun _ => True) (fun _ _ => True) (fun _ _ => False)
      (fun _ _ => True) (fun _ _ => False) (fun _ _ => False) (fun _ _ _ => False)
      (fun _ _ _ => False)
      (fun _ _ _ _ => Or.inr trivial) (fun _ _ hn => hn.elim) (fun _ _ _ hs => hs.elim)
      (fun _ _ hp => hp.elim) (fun _ _ _ hp => hp.elim) () () trivial trivial
    exact hy
  · -- without self-motion's mover
    intro h
    obtain ⟨_, hy⟩ := h Unit Unit (fun _ => True) (fun _ _ => True) (fun _ _ => True)
      (fun _ _ => False) (fun _ _ => True) (fun _ _ => False) (fun _ _ _ => False)
      (fun _ _ _ => False)
      (fun _ _ _ _ => Or.inl trivial) (fun _ _ _ => Or.inl trivial)
      (fun _ _ hf => hf.elim) (fun _ _ hp => hp.elim) (fun _ _ _ hp => hp.elim)
      () () trivial trivial
    exact hy
  · -- without the literal disjunction: a light thing's motion with no mover at all
    intro h
    obtain ⟨_, hy⟩ := h Unit Unit (fun _ => True) (fun _ _ => True) (fun _ _ => True)
      (fun _ _ => False) (fun _ _ => False) (fun _ _ => True) (fun _ _ _ => False)
      (fun _ _ _ => False)
      (fun _ _ _ _ => Or.inl trivial) (fun _ _ _ => Or.inr trivial)
      (fun _ _ hf => hf.elim) (fun _ _ _ hs => hs.elim) (fun _ _ _ _ hp => hp.elim)
      () () trivial trivial
    exact hy
  · -- without the added premise: moved only by the remover of a hindrance
    intro h
    obtain ⟨_, hy⟩ := h Unit Unit (fun _ => True) (fun _ _ => True) (fun _ _ => True)
      (fun _ _ => False) (fun _ _ => False) (fun _ _ => True) (fun _ _ _ => False)
      (fun _ _ _ => True)
      (fun _ _ _ _ => Or.inl trivial) (fun _ _ _ => Or.inr trivial)
      (fun _ _ hf => hf.elim) (fun _ _ _ hs => hs.elim)
      (fun _ _ _ => ⟨(), Or.inr trivial⟩) () () trivial trivial
    exact hy

end TruthCore.Results.Aristotle.Physics.Typed.EveryPhysicalMotionHasAPerSeMover
