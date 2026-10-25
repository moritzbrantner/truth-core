import TruthCore.Comparison.Resurrection

namespace TruthCore.History.Resurrection
open TruthCore.Comparison.Resurrection

/-- Select the adopted bundle without introducing a new theory entity. -/
def TheoryHolds (t : Theory) (s : State) : Prop :=
  match t with
  | .catholic => Catholic s
  | .legend => Legend s
  | .hallucination => Hallucination s
  | .groupHallucination => GroupHallucination s
  | .stolenBody => StolenBody s
  | .swoon => Swoon s

/-- Computed counts for all fifteen shared questions. These are availability
counts; AnswersHold proves that each available cell really follows. Every
bundle accepts the six findings, so those six counts represent positing the
findings, not independent historical explanation. -/
def CountsTable : Prop :=
  entailedCount .catholic = 15 ∧ unexplainedCount .catholic = 0 ∧
  entailedCount .legend = 8 ∧ unexplainedCount .legend = 7 ∧
  entailedCount .hallucination = 8 ∧ unexplainedCount .hallucination = 7 ∧
  entailedCount .groupHallucination = 8 ∧ unexplainedCount .groupHallucination = 7 ∧
  entailedCount .stolenBody = 9 ∧ unexplainedCount .stolenBody = 6 ∧
  entailedCount .swoon = 9 ∧ unexplainedCount .swoon = 6 ∧
  auxiliaryCount .catholic = 1 ∧ auxiliaryCount .legend = 1 ∧
  auxiliaryCount .hallucination = 1 ∧ auxiliaryCount .groupHallucination = 1 ∧
  auxiliaryCount .stolenBody = 2 ∧ auxiliaryCount .swoon = 1

/-- Answer-map consequence and the exact printed count table. This certifies
bookkeeping and projections from open commitments, not historical truth,
causal adequacy or comparative superiority. The coverage part is a
transcription of the adopted bundles; it closes no historical frontier node. -/
def AnswerMapsCorrect : Prop :=
  (∀ t s, TheoryHolds t s → AnswersHold t s) ∧ CountsTable
end TruthCore.History.Resurrection
