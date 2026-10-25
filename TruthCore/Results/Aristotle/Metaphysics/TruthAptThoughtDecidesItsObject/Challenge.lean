import TruthCore.Greek.Aristotle.MetaphysicsIV7
namespace TruthCore.Results.Aristotle.Metaphysics.TruthAptThoughtDecidesItsObject
open TruthCore.Greek.Aristotle.Metaphysics
/-- *Metaphysics* IV.7, 1012a2-5, reading A: a thought that is true or false is
an affirmation or a denial, and it is true or false by composition; so a
thought that is true or false settles its object. Four cases (affirmation or denial, true or
false). This excludes a third act of thought that is true or false, the intermediate. It
says nothing about an object that no thought has yet settled, which is where the
intuitionist withholds. -/
theorem truthAptThoughtDecidesItsObject {Thought : Type}
    (object : Thought → Prop) (Affirms Denies TrueT FalseT : Thought → Prop)
    (hDefinition : TruthAptThoughtAffirmsOrDeniesReading Affirms Denies TrueT FalseT)
    (hComposition : ThoughtTrueOrFalseByCompositionReading object Affirms Denies TrueT FalseT) :
    TruthAptThoughtDecidesItsObject object TrueT FalseT := by
  sorry
end TruthCore.Results.Aristotle.Metaphysics.TruthAptThoughtDecidesItsObject
