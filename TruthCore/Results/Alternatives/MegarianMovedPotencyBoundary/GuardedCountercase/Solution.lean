module

public import TruthCore.Alternatives.MegarianMovedPotencyBoundary

@[expose] public section
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
  obtain ⟨x, r, hm⟩ := hMoved
  refine ⟨x, r, hm, ?_⟩
  intro hp
  have h := hAnalysis x r hm hp
  exact h.2 (hMegarian x r h.1)

end TruthCore.Results.Alternatives.MegarianMovedPotencyBoundary.GuardedCountercase
