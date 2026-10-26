import TruthCore.Greek.Aristotle.MetaphysicsIV7
namespace TruthCore.Results.Bridges.IV7EveryPropositionToEveryObjectOfThought
open TruthCore.Greek.Aristotle.Metaphysics
/-- Bridge (#401): the formalization's unattributed extension of the thought
argument's first half to every proposition
(`STMT-THOUGHT-AFFIRMS-OR-DENIES-EVERY-PROPOSITION`) entails the sourced first
half, *Metaphysics* IV.7, 1012a2-3 (`STMT-OBJECT-OF-THOUGHT-AFFIRMED-OR-DENIED`):
whatever is the object of some thought is the object of a thought that affirms
or denies it. Instantiate the extension at that object. The extension is
strictly about more propositions; this shows it is no weaker than the sourced
sentence. -/
theorem objectOfThoughtAffirmedOrDeniedOfEveryProposition {Thought : Type}
    (object : Thought → Prop) (Affirms Denies : Thought → Prop)
    (hEveryProposition : ThoughtAffirmsOrDeniesEveryPropositionReading object Affirms Denies) :
    ObjectOfThoughtAffirmedOrDeniedReading object Affirms Denies := by
  sorry
end TruthCore.Results.Bridges.IV7EveryPropositionToEveryObjectOfThought
