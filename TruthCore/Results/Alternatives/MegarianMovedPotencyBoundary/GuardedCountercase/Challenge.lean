import TruthCore.Alternatives.MegarianMovedPotencyBoundary

namespace TruthCore.Results.Alternatives.MegarianMovedPotencyBoundary.GuardedCountercase
open TruthCore.Alternatives.MegarianMovedPotencyBoundary
open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics
open TruthCore.Models.MegarianCapacity

/-- Analyst obligation; source meanings and old frozen results are preserved. -/
theorem guardedCountercase {B R : Type} (MovedIn InAct InPotency CanBe : B → R → Prop)
    (hMegarian : MegarianAbilityOnlyWhenActingReading InAct CanBe)
    (hMoved : SomethingIsMovedReading MovedIn)
    (hAnalysis : AnalysisOnMoved MovedIn InAct InPotency CanBe) :
    Countertuple MovedIn InPotency := by
  sorry

end TruthCore.Results.Alternatives.MegarianMovedPotencyBoundary.GuardedCountercase
