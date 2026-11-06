module

public import TruthCore.Alternatives.MegarianMovedPotencyBoundary

@[expose] public section
namespace TruthCore.Results.Alternatives.MegarianMovedPotencyBoundary.CountercaseFailure
open TruthCore.Alternatives.MegarianMovedPotencyBoundary
open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics
open TruthCore.Models.MegarianCapacity

/-- Analyst obligation; source meanings and old frozen results are preserved. -/
theorem countercaseFailure {B R : Type} (MovedIn InPotency : B → R → Prop)
    (h : Countertuple MovedIn InPotency) : MovedPotencyFails MovedIn InPotency := by
  obtain ⟨x, r, hm, hp⟩ := h
  exact fun hLaw => hp (hLaw x r hm)

end TruthCore.Results.Alternatives.MegarianMovedPotencyBoundary.CountercaseFailure
