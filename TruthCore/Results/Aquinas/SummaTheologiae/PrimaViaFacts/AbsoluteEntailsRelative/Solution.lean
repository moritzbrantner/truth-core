import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3Interpretation
namespace TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFacts.AbsoluteEntailsRelative
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- In every motion model the absolute conclusion entails the relative one: a
mover moved by none is unmoved in every relevant respect. No premises. -/
theorem absoluteConclusionEntailsRelative : AbsoluteConclusionEntailsRelative :=
  by
  intro M hAbsolute hNoRelative
  apply hAbsolute
  intro ⟨f, ⟨x, r, hMoves⟩, hUnmoved⟩
  exact hNoRelative ⟨f, x, r, hMoves, fun r' h => hUnmoved r' h.1⟩

end TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFacts.AbsoluteEntailsRelative
