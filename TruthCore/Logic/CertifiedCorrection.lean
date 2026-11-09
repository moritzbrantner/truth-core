module

public import TruthCore.Logic.CorrectionCriterion

/-!
Analyst candidate serving the inquiry-access boundary. This is a scoped
certificate-calibrated procedure, NOT the original warranted correction sense.
Functions give explicit outputs, not a proof of human execution or computability.
Availability records execution resources; it is not epistemic entitlement.
Calibration is an open semantic premise, not philosophical justification.
No public consensus, private seeming, categorical norm or authority is encoded.
-/

@[expose] public section
namespace TruthCore.Logic.CertifiedCorrection
open TruthCore.Logic.CorrectionCriterion

/-- A Boolean decision and natural-number certificate, with a Boolean checker.
The resource predicate describes where this particular procedure can be run.
The certificate has no intrinsic authority; its interpretation is the checker. -/
structure Procedure (Evidence : Type) where
  decide : Evidence → Bool
  certificate : Evidence → Nat
  check : Evidence → Bool → Nat → Bool
  available : Evidence → Prop

/-- Execution and acceptance cover every state in the declared scope. -/
def Covered {State Evidence : Type} (p : Procedure Evidence)
    (observe : State → Evidence) (scope : State → Prop) : Prop :=
  ∀ s, scope s → p.available (observe s) ∧
    p.check (observe s) (p.decide (observe s)) (p.certificate (observe s)) = true

/-- Every accepted certificate at a scoped state correctly classifies the
supplied norm, including negative answers. This strong calibration assumption
is neither inferred from checking nor asserted to be adequate epistemic warrant. -/
def Calibrated {State Evidence : Type} (p : Procedure Evidence)
    (observe : State → Evidence) (scope Correct : State → Prop) : Prop :=
  ∀ s, scope s → ∀ b c, p.check (observe s) b c = true →
    (b = true ↔ Correct s)

/-- Coverage and calibration imply an exact classifier on the scope subtype.
No conclusion is made outside scope, or about a normative selection policy.
The `available` component of `Covered` is not load-bearing here: only the
accepted-check component is used, so resources do not enter the conclusion. -/
def ScopedConnection : Prop :=
  ∀ (State Evidence : Type) (p : Procedure Evidence) (observe : State → Evidence)
    (scope Correct : State → Prop),
    Covered p observe scope → Calibrated p observe scope Correct →
    AdmitsCriterion (fun s : {s // scope s} => observe s.val)
      (fun s => Correct s.val)

/-- Concrete checker accepts exactly the procedure's own answer. Agreement with
the checker alone can therefore be wrong. The resource switch is independent. -/
def echo (resources answer : Bool) : Procedure Bool where
  decide _ := answer
  certificate _ := 0
  check _ b _ := b == answer
  available _ := resources = true

/-- Nonvacuity, omitted calibration, classifiability without coverage, and
unlicensed scope extension controls. The third pairs a procedure-free
extensional criterion for `s = true` with the always-true echo lacking
resources: it shows only that extensional classifiability does not imply
coverage by a given procedure (that echo would also fail calibration for this
norm), not exact classification by a procedure without resources. The last
fixture is calibrated only on the true state. These finite examples do not
quantify over human epistemic practices. -/
def Controls : Prop :=
  (Covered (echo true true) (fun s : Bool => s) (fun _ => True) ∧
    Calibrated (echo true true) (fun s : Bool => s) (fun _ => True) (fun _ => True)) ∧
  (Covered (echo true true) (fun s : Bool => s) (fun _ => True) ∧
    ¬ Calibrated (echo true true) (fun s : Bool => s) (fun _ => True)
      (fun s => s = true)) ∧
  (AdmitsCriterion (fun s : Bool => s) (fun s => s = true) ∧
    ¬ Covered (echo false true) (fun s : Bool => s) (fun _ => True)) ∧
  (Calibrated (echo true true) (fun s : Bool => s) (fun s => s = true)
      (fun s => s = true) ∧
    ¬ Calibrated (echo true true) (fun s : Bool => s) (fun _ => True)
      (fun s => s = true))

def ConnectionAndControls : Prop := ScopedConnection ∧ Controls
end TruthCore.Logic.CertifiedCorrection
