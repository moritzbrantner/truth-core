module

public import TruthCore.Alternatives.MegarianMovedPotencyBoundary

@[expose] public section
namespace TruthCore.Results.Alternatives.MegarianMovedPotencyBoundary.Controls
open TruthCore.Alternatives.MegarianMovedPotencyBoundary
open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics
open TruthCore.Models.MegarianCapacity

/-- Analyst obligation; source meanings and old frozen results are preserved. -/
theorem controls : Controls := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨NothingMoved.evaluation0, ?_, ?_, NothingMoved.evaluation1⟩
    · intro x r
      constructor
      · intro h; exact False.elim h
      · intro h; exact h.1
    · intro x r h
      exact False.elim h
  · refine ⟨MovedAlreadyActual.evaluation0, MovedAlreadyActual.evaluation1, ?_, ?_⟩
    · exact fun _ _ _ => True.intro
    · intro h
      exact (h () () True.intro True.intro).2 True.intro
  · refine ⟨MovedWithoutAbility.evaluation0, MovedWithoutAbility.evaluation1, ?_, ?_⟩
    · intro x r
      constructor
      · intro h; exact False.elim h
      · intro h; exact h.1
    · exact ⟨(), (), True.intro, fun h => h⟩
  · constructor
    · intro x r h
      exact False.elim h
    · intro h
      exact ((h () ()).mp True.intro).1

end TruthCore.Results.Alternatives.MegarianMovedPotencyBoundary.Controls
