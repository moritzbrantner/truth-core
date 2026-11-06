module
public import TruthCore.Results.Comparison.ProblemOfEvil.FromDueDeficiency.Solution
@[expose] public section
namespace TruthCore.Results.Comparison.ProblemOfEvil.TruthFromDueDeficiency
open TruthCore.Comparison.ProblemOfEvil
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- Reduced transcription: the typed privation inference supplies an evil
witness, and the still-open sentence bridge supplies propositional truth. -/
theorem evilPremiseFromDueDeficiency (s : Sig)
    (hPrivation : EvilIsPrivationReading s.Evil s.Due s.Has)
    (hLacks : SomethingFallsShortOfDueGoodReading s.Due s.Has)
    (hTruth : EvilIsAsPropositionalTruthReading s.Evil s.Holds s.evilPremise) :
    EvilPremiseAssertedReading s.Holds s.evilPremise := by
  have hEvil := TruthCore.Results.Comparison.ProblemOfEvil.FromDueDeficiency.evilFromDueDeficiency
    s hPrivation hLacks
  exact hTruth hEvil
end TruthCore.Results.Comparison.ProblemOfEvil.TruthFromDueDeficiency
