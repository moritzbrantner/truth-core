import TruthCore.Greek.Aristotle.MetaphysicsIV7
import TruthCore.Results.Aristotle.Metaphysics.TruthAptThoughtDecidesItsObject.Solution
namespace TruthCore.Results.Aristotle.Metaphysics.ThoughtBivalenceIffExcludedMiddle
open TruthCore.Logic
open TruthCore.Greek.Aristotle.Metaphysics
/-- *Metaphysics* IV.7, 1012a2-5, reading B: given that thought that is true or false
affirms or denies, that thought is true or false by composition, and that every
proposition can be affirmed or denied in thought, the universal premise "every
object of thought is judged truly or falsely" holds exactly when excluded
middle does. Constructive in both directions. So reading B is not an argument
*for* excluded middle that the intuitionist must answer separately: its premise
is excluded middle restated for thought, and withholding the one is withholding
the other. -/
theorem thoughtBivalenceIffExcludedMiddle {Thought : Type}
    (object : Thought → Prop) (Affirms Denies TrueT FalseT : Thought → Prop)
    (hDefinition : TruthAptThoughtAffirmsOrDeniesReading Affirms Denies TrueT FalseT)
    (hComposition : ThoughtTrueOrFalseByCompositionReading object Affirms Denies TrueT FalseT)
    (hEvery : ThoughtAffirmsOrDeniesEveryPropositionReading object Affirms Denies) :
    ThoughtBivalenceIffExcludedMiddle object TrueT FalseT := by
  sorry
end TruthCore.Results.Aristotle.Metaphysics.ThoughtBivalenceIffExcludedMiddle
