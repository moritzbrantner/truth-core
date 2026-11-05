module
public import TruthCore.Modal.RetainedDuty
/-! Action-local minimization of #1035's frozen universal-OIC predecessors.
Analyst formulation; attribution deferred. No compensation or debt policy is
assumed by LocalOIC, even when the original-return duty is nonvacuously met. -/
@[expose] public section
namespace TruthCore.Modal.RetainedDuty
/-- Only the SAME original-return action at after, not all actions. -/
def LocalOIC (s : Case) : Prop := PresentDuty s → s.able .after .originalReturn

/-- Nonvacuous original-return OIC can coexist with failed compensation OIC. -/
def compensationBlocked : Case :=
  ⟨fun _ a => a = .originalReturn ∨ a = .compensation,
   fun _ a => a = .originalReturn, fun _ _ => False, fun _ _ => False⟩
/-- Independently, it can coexist with failed debt-repayment OIC. -/
def repaymentBlocked : Case :=
  ⟨fun _ a => a = .originalReturn ∨ a = .debtRepayment,
   fun _ a => a = .originalReturn, fun _ _ => False, fun _ _ => False⟩

/-- Single-member deletion controls for the weaker operational cores, plus
strictness witnesses with an actual original-return duty and ability. -/
def LocalControls : Prop :=
  (PresentInability noDuty ∧ LocalOIC noDuty ∧ ¬ PresentDuty noDuty) ∧
  (PresentDuty ableReturn ∧ LocalOIC ableReturn ∧ ¬ PresentInability ableReturn) ∧
  (PresentDuty crash ∧ PresentInability crash ∧ ¬ LocalOIC crash) ∧
  (Retention neverOwed ∧ PresentInability neverOwed ∧ LocalOIC neverOwed ∧
    ¬ InitialDuty neverOwed) ∧
  (InitialDuty lapse ∧ PresentInability lapse ∧ LocalOIC lapse ∧ ¬ Retention lapse) ∧
  (InitialDuty ableReturn ∧ Retention ableReturn ∧ LocalOIC ableReturn) ∧
  (InitialDuty crash ∧ Retention crash ∧ PresentInability crash) ∧
  (LocalOIC compensationBlocked ∧ ¬ PresentOIC compensationBlocked ∧
    PresentDuty compensationBlocked ∧ compensationBlocked.able .after .originalReturn ∧
    compensationBlocked.duty .after .compensation ∧
    ¬ compensationBlocked.able .after .compensation) ∧
  (LocalOIC repaymentBlocked ∧ ¬ PresentOIC repaymentBlocked ∧
    PresentDuty repaymentBlocked ∧ repaymentBlocked.able .after .originalReturn ∧
    repaymentBlocked.duty .after .debtRepayment ∧
    ¬ repaymentBlocked.able .after .debtRepayment)
end TruthCore.Modal.RetainedDuty
