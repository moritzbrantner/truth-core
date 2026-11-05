import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
namespace TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaStrength.AbsoluteReading
open TruthCore.Latin.Aquinas.SummaTheologiae
universe u v
/-- The absolute *prima via* conclusion entails the relative one for the same
relations: if a first mover moved in no respect cannot be lacking, then a mover
unmoved in every respect relevant to its moving cannot be lacking either.
Registers `STMT-FIRST-UNMOVED-MOVER-CANNOT-BE-LACKING` strengthens
`STMT-RELATIVELY-UNMOVED-MOVER-CANNOT-BE-LACKING` (#1017). -/
theorem absoluteReadingEntailsRelative {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (RelevantTo : Being → Being → Respect → Respect → Prop)
    (hAbsolute : FirstUnmovedMoverCannotBeLackingReading MovedIn MovesIn) :
    RelativelyUnmovedMoverCannotBeLackingReading MovedIn MovesIn RelevantTo := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaStrength.AbsoluteReading
