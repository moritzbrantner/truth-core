import TruthCore.Alternatives.ActPotencyRegress
namespace TruthCore.Results.Alternatives.EleaticRestSelfRefuting
open TruthCore.Alternatives.ActPotencyRegress

/-- Aristotle's retorsion against the Eleatic thesis (*Physics* VIII.3,
254a27-30): if anyone opines that nothing is moved, then, since opining is a
being moved, the opiner is moved in the respect of that very opinion, and the
thesis is false. The thesis is refuted by the act of holding it. -/
theorem eleaticThesisFalse {Being Respect : Type}
    (MovedIn : Being → Respect → Prop) (Opines : Being → Prop → Prop)
    (asOpinion : Prop → Respect)
    (hOpinionIsMotion : OpiningIsBeingMovedReading MovedIn Opines asOpinion)
    (hHeld : EleaticThesisIsOpinedReading MovedIn Opines) :
    EleaticThesisFalse MovedIn := by
  intro hNothingMoved
  -- Someone opines the thesis.
  obtain ⟨x, hOpines⟩ := hHeld
  -- Opining it is being moved in the respect of that opinion.
  have hMoved : MovedIn x (asOpinion (NothingIsMovedReading MovedIn)) :=
    hOpinionIsMotion x _ hOpines
  -- But the thesis says that nothing is moved in any respect.
  exact hNothingMoved x _ hMoved

/-- The premise that opining is a motion is needed: one being that opines the
thesis and is moved in no respect satisfies the other premise and the thesis. -/
theorem needsOpinionIsMotion :
    ¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (Opines : Being → Prop → Prop),
      EleaticThesisIsOpinedReading MovedIn Opines → EleaticThesisFalse MovedIn := by
  intro h
  exact h Unit Unit (fun _ _ => False) (fun _ _ => True) ⟨(), trivial⟩
    (fun _ _ hMoved => hMoved)

/-- The premise that the thesis is held is needed: where nobody opines anything
and nothing is moved, opining is vacuously a motion and the thesis is true. -/
theorem needsThesisHeld :
    ¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (Opines : Being → Prop → Prop) (asOpinion : Prop → Respect),
      OpiningIsBeingMovedReading MovedIn Opines asOpinion →
        EleaticThesisFalse MovedIn := by
  intro h
  exact h Unit Unit (fun _ _ => False) (fun _ _ => False) (fun _ => ())
    (fun _ _ hOpines => hOpines) (fun _ _ hMoved => hMoved)

end TruthCore.Results.Alternatives.EleaticRestSelfRefuting
