import TruthCore.Comparison.ProblemOfEvil
namespace TruthCore.Results.Comparison.ProblemOfEvil.CatholicEntailsEvilPremise
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Comparison.ProblemOfEvil
theorem catholicEntailsEvilPremise (s : Sig) (hBackground : Background s)
    (hCatholic : Catholic s) : EvilPremiseAssertedReading s.Holds s.evilPremise := by
  sorry
end TruthCore.Results.Comparison.ProblemOfEvil.CatholicEntailsEvilPremise
