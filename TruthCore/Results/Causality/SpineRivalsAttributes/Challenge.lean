import TruthCore.Causality.SpineRivalsAttributes

/-! Finite tests of the rivals of the stage-two attribute premises. Each lemma
checks one interpretation of `TruthCore.Causality.SpineRivalsAttributes.Control`:
the rival holds, every other premise of the named consuming theorem holds, and
that theorem's conclusion fails. Model claims concern these interpretations
only. -/

namespace TruthCore.Results.Causality.SpineRivalsAttributes

open TruthCore.Causality.SpineRivalsAttributes
open TruthCore.Causality.SpineRivalsAttributes.Control
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Alternatives.FideismReference
open TruthCore.Alternatives.NameApplicationTransfer
open TruthCore.Causality.CausalMapsBatch1
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessaryFirstBeing
open TruthCore.Causality.NecessaryFirstAttributes
open TruthCore.Causality.Round2ExistenceAct
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.PureActThisness (FirstMoverHasEveryPureDetermination)
open TruthCore.Causality.WholePowerPerfection (InfiniteHasEveryPurePerfection)
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)

/-- The fourteen finite tests. -/
theorem controls : TruthCore.Causality.SpineRivalsAttributes.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.SpineRivalsAttributes
