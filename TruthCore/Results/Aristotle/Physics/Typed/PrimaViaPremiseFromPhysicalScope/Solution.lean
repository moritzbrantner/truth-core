import TruthCore.Greek.Aristotle.Physics.Typed.Motion
namespace TruthCore.Results.Aristotle.Physics.Typed.PrimaViaPremiseFromPhysicalScope
open TruthCore.Greek.Aristotle.Physics.Typed
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- The scope step from *Physics* VIII.4 to the *prima via*: if every physical motion
has a per se mover in its respect, and every respect in which something is being
moved is a respect of physical motion (an added, unattributed scope premise), then
whatever is moved in a respect has a mover in that respect.

This step only composes the restricted conclusion with the scope premise; its
content is the scope premise, which is open. -/
theorem primaViaPremiseFromPhysicalScope {Being : Type} {Respect : Type}
    (IsPhysicalRespect : Respect → Prop)
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (hPhysical : EveryPhysicalMotionHasAPerSeMoverReading IsPhysicalRespect MovedIn MovesIn)
    (hScope : EveryReductionIsPhysicalMotionReading IsPhysicalRespect MovedIn) :
    ReducedOnlyByAMoverReading MovedIn MovesIn := by
  -- INF-ARIST-PHYS-VIII-4-SCOPE-BRIDGE-TO-PRIMA-VIA
  intro x r hMoved
  exact hPhysical x r (hScope x r hMoved) hMoved

/-- Both premises are needed. Without the scope premise, a being moved in a
non-physical respect has no mover although every physical motion has one; without
the restricted conclusion, a physical motion has no mover. -/
theorem premisesNeeded :
    (¬ ∀ (Being Respect : Type) (IsPhysicalRespect : Respect → Prop)
        (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop),
      EveryPhysicalMotionHasAPerSeMoverReading IsPhysicalRespect MovedIn MovesIn →
      ReducedOnlyByAMoverReading MovedIn MovesIn) ∧
    (¬ ∀ (Being Respect : Type) (IsPhysicalRespect : Respect → Prop)
        (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop),
      EveryReductionIsPhysicalMotionReading IsPhysicalRespect MovedIn →
      ReducedOnlyByAMoverReading MovedIn MovesIn) := by
  refine ⟨?_, ?_⟩
  · intro h
    obtain ⟨_, hy⟩ := h Unit Unit (fun _ => False) (fun _ _ => True) (fun _ _ _ => False)
      (fun _ _ hp => hp.elim) () () trivial
    exact hy
  · intro h
    obtain ⟨_, hy⟩ := h Unit Unit (fun _ => True) (fun _ _ => True) (fun _ _ _ => False)
      (fun _ _ _ => trivial) () () trivial
    exact hy

end TruthCore.Results.Aristotle.Physics.Typed.PrimaViaPremiseFromPhysicalScope
