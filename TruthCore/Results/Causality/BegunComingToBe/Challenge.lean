import TruthCore.Causality.BegunComingToBe
import TruthCore.Results.Causality.ContingentComingToBe.Solution

namespace TruthCore.Results.Causality.BegunComingToBe
open TruthCore.Causality.BegunComingToBe
open TruthCore.Causality.ContingentComingToBe (PossiblyFoundedComingToBe)
open TruthCore.Causality.InertEmptiness (PossiblyContingentsAbsentThenPresent)
open TruthCore.Modal.TemporalHistory (History)

/-- Strength order: founded coming-to-be gives begun coming-to-be. -/
theorem possiblyBegunOfFounded {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (w : W)
    (hFounded : PossiblyFoundedComingToBe h Concrete w) :
    PossiblyBegunComingToBe h Concrete w := by
  sorry

/-- The possibility of begun coming-to-be gives the possible contingent-free
past (premise A3 of the modal spine). -/
theorem possibleContingentFreePast {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (w : W)
    (hPossible : PossiblyBegunComingToBe h Concrete w) :
    PossiblyContingentsAbsentThenPresent h Concrete w := by
  sorry

/-- Strictness and nonvacuity control in a history with a beginning and no
earliest moment after it. -/
theorem controls : Control.Certificate := by
  sorry

end TruthCore.Results.Causality.BegunComingToBe
