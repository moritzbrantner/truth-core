import TruthCore.Comparison.Fideism
namespace TruthCore.Results.Alternatives.FideismCatholicPractice
open TruthCore.Alternatives.Fideism

/-- Defeat by consequence of Wittgensteinian fideism (WF-N) as a description of
the Catholic practice (#1010). If the practice's council defines a move that
affirms God's knowability from created things by the natural light of reason
(*Dei Filius* ch. 2, can. II.1), if what the council defines is endorsed by the
practice's own standards, and if that natural reason is reason shared with
those outside the practice, then the fideist pair fails: by its internal-grammar
thesis the defined move is correct, and by its cut-off thesis it is not.
None of the three premises is a fideist commitment, and none is established. -/
theorem fideismFailsAsDescription (P : Practice)
    (hCouncil : CouncilDefinesNaturalKnowabilityReading P)
    (hDefinition : DefinitionIsOwnStandardReading P)
    (hShared : NaturalReasonIsSharedReading P) :
    FideismFailsAsDescription P := by
  sorry

/-- The council premise is needed: a practice whose only move is endorsed by
its own standards, answers to nothing shared, and is not a defined
natural-knowability move satisfies the fideist pair and both bridges. -/
theorem needsCouncil :
    ¬ ∀ P : Practice, DefinitionIsOwnStandardReading P → NaturalReasonIsSharedReading P →
      FideismFailsAsDescription P := by
  sorry

/-- The definition bridge is needed (the escape of a fideist who treats
conciliar teaching as theology about the practice, not part of its grammar):
the defined natural-knowability move answers to shared reason, is not endorsed
by the practice's own standards, and is not correct. -/
theorem needsDefinitionIsOwnStandard :
    ¬ ∀ P : Practice, CouncilDefinesNaturalKnowabilityReading P →
      NaturalReasonIsSharedReading P → FideismFailsAsDescription P := by
  sorry

/-- The shared-reason reading is needed (the practice-internal re-reading of
"naturali humanae rationis lumine", `DISAMB-NATURAL-REASON`): the defined move
is endorsed and correct but answers to nothing shared, so the fideist pair
holds. -/
theorem needsNaturalReasonIsShared :
    ¬ ∀ P : Practice, CouncilDefinesNaturalKnowabilityReading P →
      DefinitionIsOwnStandardReading P → FideismFailsAsDescription P := by
  sorry

end TruthCore.Results.Alternatives.FideismCatholicPractice
