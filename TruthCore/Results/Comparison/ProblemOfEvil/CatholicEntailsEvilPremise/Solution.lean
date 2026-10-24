import TruthCore.Comparison.ProblemOfEvil
namespace TruthCore.Results.Comparison.ProblemOfEvil.CatholicEntailsEvilPremise
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Comparison.ProblemOfEvil
theorem catholicEntailsEvilPremise (s : Sig) (hBackground : Background s)
    (hCatholic : Catholic s) : EvilPremiseAssertedReading s.Holds s.evilPremise := by
  obtain ⟨_, hPrivation, hTruth, ⟨x, p, hDue, hLacks⟩, _⟩ := hCatholic
  -- INF-CATHOLIC-EVIL-EXISTS: a due good is lacking (q.48 a.2), and that lack is evil (q.48 a.3).
  have hEvil : ∃ x, s.Evil x := ⟨x, (hPrivation x).mpr ⟨p, hDue, hLacks⟩⟩
  -- INF-CATHOLIC-GROUNDING-ENTAILS-EVIL-PREMISE: so "there is evil" is true (q.48 a.2 ad 2).
  exact hTruth hEvil
end TruthCore.Results.Comparison.ProblemOfEvil.CatholicEntailsEvilPremise
