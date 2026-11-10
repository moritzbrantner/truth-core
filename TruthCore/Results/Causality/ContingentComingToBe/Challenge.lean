import TruthCore.Causality.ContingentComingToBe
import TruthCore.Results.Causality.InertEmptiness.Solution

namespace TruthCore.Results.Causality.ContingentComingToBe
open TruthCore.Causality.ContingentComingToBe
open TruthCore.Causality.InertEmptiness (ContingentsAbsentThenPresentAt
  PossiblyContingentsAbsentThenPresent)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Modal.TemporalHistory (History)

/-- The possibility of founded coming-to-be gives the possible contingent-free
past (premise A3 of the modal spine). No frame condition, presence contract or
inertness of emptiness is used. -/
theorem possibleContingentFreePast {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (w : W)
    (hPossible : PossiblyFoundedComingToBe h Concrete w) :
    PossiblyContingentsAbsentThenPresent h Concrete w := by
  sorry

/-- Survival models of the initial-state rival and a witness of the new premise. -/
theorem controls : Control.Certificate := by
  sorry

end TruthCore.Results.Causality.ContingentComingToBe
