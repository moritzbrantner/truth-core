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
  intro t hApt
  -- "Clear from the definition": a true or false thought affirms or denies.
  cases hDefinition t hApt with
  | inl hAffirms =>
    have hRule := (hComposition t).1 hAffirms
    cases hApt with
    | inl hTrue =>
      -- A true affirmation: its object holds.
      exact Or.inl (hRule.1.mp hTrue)
    | inr hFalse =>
      -- A false affirmation: its object does not hold.
      exact Or.inr (hRule.2.mp hFalse)
  | inr hDenies =>
    have hRule := (hComposition t).2 hDenies
    cases hApt with
    | inl hTrue =>
      -- A true denial: its object does not hold.
      exact Or.inr (hRule.1.mp hTrue)
    | inr hFalse =>
      -- A false denial: its object holds.
      exact Or.inl (hRule.2.mp hFalse)
end TruthCore.Results.Aristotle.Metaphysics.TruthAptThoughtDecidesItsObject
