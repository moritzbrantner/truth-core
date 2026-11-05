import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
namespace TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaStrength.PerSeLink
open TruthCore.Latin.Aquinas.SummaTheologiae
universe u v
/-- The strong per se link reading entails the relevant-respect reading: a
second mover that moves only insofar as it is moved (in any respect) is in
particular a per se link when it is moved in a respect relevant to its moving.
Registers `STMT-SECOND-MOVERS-MOVE-ONLY-AS-MOVED` strengthens
`STMT-SECOND-MOVERS-MOVE-AS-MOVED-IN-RELEVANT-RESPECT` (#1017). -/
theorem secondMoversStrongEntailsRelevantRespect {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (MovesAsMoved : Being → Being → Prop)
    (RelevantTo : Being → Being → Respect → Respect → Prop)
    (hStrong : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved) :
    SecondMoversMoveAsMovedInRelevantRespectReading MovedIn MovesIn MovesAsMoved RelevantTo := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaStrength.PerSeLink
