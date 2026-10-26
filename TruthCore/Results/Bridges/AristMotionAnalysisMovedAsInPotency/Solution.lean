import TruthCore.Greek.Aristotle.Physics
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
namespace TruthCore.Results.Bridges.AristMotionAnalysisMovedAsInPotency
open TruthCore.Greek.Aristotle.Physics
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- Bridge (#401): Aristotle's definition of motion, *Physics* III.1, 201a10-11
(`STMT-BEING-MOVED-IS-ACTUALIZATION-OF-POTENCY`: a being is moved in a respect
exactly when it is in potency to it and that potency, as potency, is being
actualized), entails the prima via's premise
(`STMT-NOTHING-MOVED-EXCEPT-AS-IN-POTENCY`): whatever is moved in a respect is
in potency to it. Only the left-to-right half of the definition and its first
conjunct are used.

As for potency, `ActPotencyDefinitionalAnalysesConservative` shows the
definition is no stronger than the premise; this bridge moves the premise's
openness to the Aristotle reading and does not discharge it. -/
theorem movedOnlyAsInPotencyOfMotionDefinition {Being Respect : Type}
    (MovedIn InPotency ActualizedQuaPotential : Being → Respect → Prop)
    (hDefinition : BeingMovedIsActualizationOfPotencyReading
      MovedIn InPotency ActualizedQuaPotential) :
    MovedOnlyAsInPotencyReading MovedIn InPotency := by
  intro x r hMoved
  -- Being moved is being in potency and having that potency actualized.
  have hAnalysed := (hDefinition x r).mp hMoved
  exact hAnalysed.1
end TruthCore.Results.Bridges.AristMotionAnalysisMovedAsInPotency
