module
public import TruthCore.Results.Causality.CountCauseTimeNecessity.Solution
@[expose] public section
namespace TruthCore.Results.Causality.CountCauseTimeOpportunity
open TruthCore.Causality.CountTemporalNecessity
open TruthCore.Causality.CountCauseTimeNecessity
open TruthCore.Modal.TemporalHistory

/-- Register the existing checked two-input helper without changing its meaning
or rediscovering its five-to-one/selected-cause-time guard specialization. -/
theorem opportunityOfThresholds {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (CauseCount : W → B → Nat → T → Prop) (w : W)
    (hFive : FiveThresholdPossible h Concrete CauseCount w)
    (hDescent : ThresholdDescent h Concrete CauseCount w) :
    CauseTimeOpportunity h Concrete CauseCount w := by
  exact TruthCore.Results.Causality.CountCauseTimeNecessity.opportunityOfOld
    h Concrete CauseCount w hFive hDescent
end TruthCore.Results.Causality.CountCauseTimeOpportunity
