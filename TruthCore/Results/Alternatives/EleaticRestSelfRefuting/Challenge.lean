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
  sorry

/-- The premise that opining is a motion is needed: one being that opines the
thesis and is moved in no respect satisfies the other premise and the thesis. -/
theorem needsOpinionIsMotion :
    ¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (Opines : Being → Prop → Prop),
      EleaticThesisIsOpinedReading MovedIn Opines → EleaticThesisFalse MovedIn := by
  sorry

/-- The premise that the thesis is held is needed: where nobody opines anything
and nothing is moved, opining is vacuously a motion and the thesis is true. -/
theorem needsThesisHeld :
    ¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (Opines : Being → Prop → Prop) (asOpinion : Prop → Respect),
      OpiningIsBeingMovedReading MovedIn Opines asOpinion →
        EleaticThesisFalse MovedIn := by
  sorry

end TruthCore.Results.Alternatives.EleaticRestSelfRefuting
