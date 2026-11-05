module

public import TruthCore.Results.Modal.DeonticFutureBoundary.Solution
public import TruthCore.Logic.Configuration

/-! Logic-first working reconstruction for #1035. Attribution is deferred.
Duty, ability, actual fulfillment and responsibility are independent inputs;
no moral fact is inferred from a crash or a bank balance. -/

@[expose] public section
namespace TruthCore.Modal.RetainedDuty
open DeonticFutureBoundary

/-- Three dated stages of one borrower's case, not alternative possible worlds. -/
inductive Stage where | before | after | later
  deriving DecidableEq
/-- Returning the very same object, paying compensation and repaying a loan
are different performances. No substitution rule is built into these names. -/
inductive Action where | originalReturn | compensation | debtRepayment
  deriving DecidableEq

/-- One fixed agent throughout; adding agents would not alter the local core.
Ability is practical ability at a date, not permission or actual performance.
Responsibility is retrospective accountability for an action-indexed episode,
not a current duty to perform an impossible act. All fields are stipulated. -/
structure Case where
  duty : Stage → Action → Prop
  able : Stage → Action → Prop
  fulfilled : Stage → Action → Prop
  responsible : Stage → Action → Prop

def PresentDuty (s : Case) : Prop := s.duty .after .originalReturn
def PresentInability (s : Case) : Prop := ¬ s.able .after .originalReturn
def PresentOIC (s : Case) : Prop := ∀ a, s.duty .after a → s.able .after a
def InitialDuty (s : Case) : Prop := s.duty .before .originalReturn
/-- Persistence for the SAME original-return action across the loss event.
This is a moral policy, not a transition law supplied by scenario description. -/
def Retention (s : Case) : Prop :=
  s.duty .before .originalReturn → s.duty .after .originalReturn

/-- Strict chronological future in this three-stage finite example. Nested
exhaustive cases avoid the `propext` dependency that Lean generates for an
overlapping multi-discriminant proposition match; the truth table is unchanged. -/
def laterFrame : Frame Stage := ⟨fun t u =>
  match t with
  | .before => match u with
    | .before => False
    | .after => True
    | .later => True
  | .after => match u with
    | .before => False
    | .after => False
    | .later => True
  | .later => False⟩
def FutureCan (s : Case) (t : Stage) (a : Action) : Prop :=
  Can laterFrame t (fun u => s.able u a)
def FutureOIC (s : Case) : Prop := ∀ a, s.duty .after a → FutureCan s .after a

/-- Full future repair needs BOTH an explicit duty-to-ideal interpretation
and overlap of ideal with genuinely feasible dates; compatibility is imported,
not rediscovered. Future feasibility does not assert actual fulfillment. -/
theorem futureRepair (s : Case) (ideal : Frame Stage)
    (interpretation : ∀ a, s.duty .after a → Ought ideal .after (fun u => s.able u a))
    (overlap : ∃ u, ideal.access .after u ∧ laterFrame.access .after u) :
    FutureOIC s := by
  intro a ha
  exact (compatibility ideal laterFrame Stage.after).mpr overlap _ (interpretation a ha)

/-- Three local omission controls: omit duty, inability, or present OIC. -/
def noDuty : Case := ⟨fun _ _ => False, fun _ _ => False,
  fun _ _ => False, fun _ _ => False⟩
def ableReturn : Case := ⟨fun _ a => a = .originalReturn, fun _ _ => True,
  fun _ _ => False, fun _ _ => False⟩
/-- Destroyed original: duty retained at every stage, return ability only before
crash, accountability retained after crash, no actual fulfillment. Compensation
can become available later, but is not identified with returning the original. -/
def crash : Case := ⟨fun _ a => a = .originalReturn,
  fun t a => match a with
    | .originalReturn => t = .before
    | .compensation => t = .later
    | .debtRepayment => False,
  fun _ _ => False,
  fun t a => t = .after ∧ a = .originalReturn⟩
/-- Initial duty lapses at the crash. Responsibility remains: the strongest
present-OIC reply can deny retention without erasing retrospective accountability. -/
def lapse : Case := { crash with duty := fun t a => t = .before ∧ a = .originalReturn }
/-- No original duty before or after; persistence holds with false antecedent.
The other full-core assumptions hold. A control, not a moral explanation. -/
def neverOwed : Case := { crash with duty := fun _ _ => False }
/-- A debtor without current funds may have feasible future funds while never
actually paying. Debt duty is explicitly stipulated, not inferred from a loan. -/
def debt : Case := ⟨fun _ a => a = .debtRepayment,
  fun t a => t = .later ∧ a = .debtRepayment,
  fun _ _ => False, fun _ _ => False⟩

/-- Certified direct-core deletions, all four full-core deletions, and controls
separating future ability, actual fulfillment, accountability and action identity.
Includes the OLD imported certificate as reuse, not new overlap discovery. -/
def Controls : Prop :=
  (PresentInability noDuty ∧ PresentOIC noDuty ∧ ¬ PresentDuty noDuty) ∧
  (PresentDuty ableReturn ∧ PresentOIC ableReturn ∧ ¬ PresentInability ableReturn) ∧
  (PresentDuty crash ∧ PresentInability crash ∧ ¬ PresentOIC crash) ∧
  (Retention neverOwed ∧ PresentInability neverOwed ∧ PresentOIC neverOwed ∧
    ¬ InitialDuty neverOwed) ∧
  (InitialDuty lapse ∧ PresentInability lapse ∧ PresentOIC lapse ∧ ¬ Retention lapse ∧
    lapse.responsible .after .originalReturn ∧ ¬ PresentDuty lapse) ∧
  (InitialDuty ableReturn ∧ Retention ableReturn ∧ PresentOIC ableReturn) ∧
  (InitialDuty crash ∧ Retention crash ∧ PresentInability crash) ∧
  (FutureOIC debt ∧ ¬ debt.able .after .debtRepayment ∧
    (∀ t, ¬ debt.fulfilled t .debtRepayment)) ∧
  (crash.responsible .after .originalReturn ∧
    ¬ FutureCan crash .after .originalReturn ∧
    FutureCan crash .after .compensation ∧
    ¬ crash.duty .after .compensation ∧ ¬ FutureOIC crash) ∧
  (∀ (s : Case) (i : Frame Stage),
    (∀ a, s.duty .after a → Ought i .after (fun u => s.able u a)) →
    (∃ u, i.access .after u ∧ laterFrame.access .after u) → FutureOIC s) ∧
  DeonticFutureBoundary.Certificate
/-- Complete choice futures, each containing its own dated action profile.
The actual branch is separately designated and need not realize an available
fulfilling future. Unlike Stage these alternatives are not successive dates. -/
inductive Branch where | missed | recovery
  deriving DecidableEq
structure Plan where
  current : Case
  feasible : Branch → Prop
  ideal : Branch → Prop
  actual : Branch
  ability : Branch → Stage → Action → Prop
  performance : Branch → Stage → Action → Prop

def BranchAbility (p : Plan) (b : Branch) (a : Action) : Prop :=
  ∃ t, laterFrame.access .after t ∧ p.ability b t a
def FeasibleAbility (p : Plan) (a : Action) : Prop :=
  Can ⟨fun _ b => p.feasible b⟩ p.actual (fun b => BranchAbility p b a)
def BranchOIC (p : Plan) : Prop :=
  ∀ a, p.current.duty .after a → FeasibleAbility p a
/-- The same imported compatibility theorem, now applied to complete dated
choice futures rather than to dates. Both semantic bridges remain explicit. -/
theorem branchRepair (p : Plan)
    (interpretation : ∀ a, p.current.duty .after a →
      Ought ⟨fun _ b => p.ideal b⟩ p.actual (fun b => BranchAbility p b a))
    (overlap : ∃ b, p.ideal b ∧ p.feasible b) : BranchOIC p := by
  intro a ha
  exact (compatibility ⟨fun _ b => p.ideal b⟩
    ⟨fun _ b => p.feasible b⟩ p.actual).mpr overlap _ (interpretation a ha)

/-- No recovery in the actual history, despite a stipulated feasible recovery
alternative. All dated actual abilities agree with current.able; no actual
performance is asserted by the feasible alternative's ability. -/
def debtPlan : Plan :=
  ⟨{ debt with able := fun _ _ => False }, fun _ => True,
    fun b => b = .recovery, .missed,
    (fun b t a => b = .recovery ∧ t = .later ∧ a = .debtRepayment),
    (fun b t a => b = .recovery ∧ t = .later ∧ a = .debtRepayment)⟩

def BranchControls : Prop :=
  (∀ (p : Plan),
    (∀ a, p.current.duty .after a →
      Ought ⟨fun _ b => p.ideal b⟩ p.actual (fun b => BranchAbility p b a)) →
    (∃ b, p.ideal b ∧ p.feasible b) → BranchOIC p) ∧
  (BranchOIC debtPlan ∧ debtPlan.current.duty .after .debtRepayment ∧
    ¬ debtPlan.current.able .after .debtRepayment ∧
    ¬ BranchAbility debtPlan debtPlan.actual .debtRepayment ∧
    (∀ t, ¬ debtPlan.performance debtPlan.actual t .debtRepayment) ∧
    (∀ t a, debtPlan.ability debtPlan.actual t a ↔ debtPlan.current.able t a) ∧
    ¬ FeasibleAbility debtPlan .originalReturn)
end TruthCore.Modal.RetainedDuty
