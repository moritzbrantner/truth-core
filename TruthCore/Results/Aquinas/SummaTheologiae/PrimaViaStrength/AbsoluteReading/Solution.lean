module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3

@[expose] public section

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
  intro hNoRelative
  apply hAbsolute
  intro ⟨f, ⟨x, r, hMoves⟩, hUnmoved⟩
  exact hNoRelative ⟨f, x, r, hMoves, fun r' h => hUnmoved r' h.1⟩
end TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaStrength.AbsoluteReading
