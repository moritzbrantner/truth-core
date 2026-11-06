module

public import TruthCore.Alternatives.MegarianMovedPotencyBoundary

@[expose] public section
namespace TruthCore.Results.Alternatives.MegarianMovedPotencyBoundary.AnalysisStrength
open TruthCore.Alternatives.MegarianMovedPotencyBoundary
open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics
open TruthCore.Models.MegarianCapacity

/-- Analyst obligation; source meanings and old frozen results are preserved. -/
theorem analysisStrength {B R : Type} (MovedIn InAct InPotency CanBe : B → R → Prop)
    (h : PotencyIsUnactualizedCapacityReading InAct InPotency CanBe) :
    AnalysisOnMoved MovedIn InAct InPotency CanBe := by
  exact fun x r _ hp => (h x r).mp hp

end TruthCore.Results.Alternatives.MegarianMovedPotencyBoundary.AnalysisStrength
