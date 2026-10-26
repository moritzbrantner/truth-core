import TruthCore.Greek.Aristotle.MetaphysicsIV7
namespace TruthCore.Results.Bridges.IV7ReadingBHalvesYieldBivalence
open TruthCore.Greek.Aristotle.Metaphysics
/-- Bridge (#401): the two halves of the thought argument's universal reading,
*Metaphysics* IV.7, 1012a2-4, yield bivalence of thought. The formalization's
extension of the first half to every proposition
(`STMT-THOUGHT-AFFIRMS-OR-DENIES-EVERY-PROPOSITION`, unattributed) and the sourced
second half (`STMT-AFFIRMING-OR-DENYING-THOUGHT-IS-TRUE-OR-FALSE`) give
`STMT-EVERY-OBJECT-OF-THOUGHT-JUDGED-TRULY-OR-FALSELY`: for every proposition
some thought with that object is true or false. No excluded middle is used here;
`ARIST-MET-1012A-THOUGHT-BIVALENCE-IFF-EXCLUDED-MIDDLE` shows the conclusion is
equivalent to it given the other readings. -/
theorem everyObjectOfThoughtJudgedOfReadingBHalves {Thought : Type}
    (object : Thought → Prop) (Affirms Denies TrueT FalseT : Thought → Prop)
    (hEveryProposition : ThoughtAffirmsOrDeniesEveryPropositionReading object Affirms Denies)
    (hTrueOrFalse : AffirmingOrDenyingThoughtIsTrueOrFalseReading Affirms Denies TrueT FalseT) :
    EveryObjectOfThoughtJudgedTrulyOrFalselyReading object TrueT FalseT := by
  sorry
end TruthCore.Results.Bridges.IV7ReadingBHalvesYieldBivalence
