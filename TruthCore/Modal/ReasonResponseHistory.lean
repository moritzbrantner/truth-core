module

public import TruthCore.Modal.ChoiceContext
public import TruthCore.Logic.CorrectionCriterion

/-!
Analyst two-stage intervention model for #1082 under #945; attribution deferred.
Earlier review and external-setting inputs acquire the current decision law.
The exact existing ChoiceContext action then uses that law, a reason-signal
preference and an imposed constraint. Copying review or external setting is a
toy mechanism interpretation, not independently established agency/causation.
Input sensitivity, intervention dependence and normative historical ownership
are different. No freedom, desert, real applicability or ultimate sourcehood
follows; an incompatibilist may reject both deterministic mechanisms as free.
-/

@[expose] public section

namespace TruthCore.Modal.ReasonResponseHistory
open ChoiceContext
open TruthCore.Logic.CorrectionCriterion

abbrev Acquisition := Bool → Bool → Bool

/-- Review-input route; the input name supplies no autonomy or agency premise. -/
def selfReview : Acquisition := fun review _ => review

/-- External-setting route; no real manipulation diagnosis is asserted. -/
def externalBypass : Acquisition := fun _ external => external

/-- The acquired selector is the old table's law, not a change to its response
function. The other two old inputs remain explicitly represented. -/
def record (acquire : Acquisition) (review external reason imposed : Bool) : History :=
  ⟨acquire review external, reason, imposed⟩

def run (acquire : Acquisition) (review external reason imposed : Bool) : Bool :=
  action (record acquire review external reason imposed)

/-- A complete current table record plus its entire reason-response function
at the same acquired selector and constraint status. This is more information
than the actual action alone, but omits how the selector was acquired. -/
abbrev PresentData := History × (Bool → Bool)

def observe (acquire : Acquisition) : PresentData :=
  (record acquire false false true false,
    fun reason => run acquire false false reason false)

/-- Sensitivity to this one-bit signal, not correctness of reasons, rational
receptivity or a sufficient condition of freedom/responsibility. -/
def SignalSensitive (acquire : Acquisition) : Prop :=
  ∀ review external,
    run acquire review external false false ≠ run acquire review external true false

/-- Actual action-changing intervention on the earlier review input while the
external setting, reason signal and absence of imposed override stay fixed. -/
def ReviewInfluence (acquire : Acquisition) : Prop :=
  ∃ review, run acquire review false true false ≠ run acquire false false true false

/-- The corresponding intervention on external acquisition input. Neither
predicate asserts an ability under exactly the same past and laws. -/
def ExternalInfluence (acquire : Acquisition) : Prop :=
  ∃ external, run acquire false external true false ≠ run acquire false false true false

/-- One joint comparison, importing the existing classifier factorization.
The override clause marks a downstream omission boundary; revealing acquisition
information repairs exact classification without proving normative ownership. -/
def Certificate : Prop :=
  (∀ (acquire : Acquisition) review external review' external' reason imposed,
    acquire review external = acquire review' external' →
    run acquire review external reason imposed = run acquire review' external' reason imposed) ∧
  (∀ acquire, SignalSensitive acquire) ∧
  (observe selfReview = observe externalBypass ∧
    action (observe selfReview).1 = action (observe externalBypass).1 ∧
    ReviewInfluence selfReview ∧ ¬ ExternalInfluence selfReview ∧
    ExternalInfluence externalBypass ∧ ¬ ReviewInfluence externalBypass) ∧
  (∀ P : Acquisition → Prop, AdmitsCriterion observe P ↔ FiberInvariant observe P) ∧
  (¬ AdmitsCriterion observe ReviewInfluence ∧
    ¬ AdmitsCriterion observe ExternalInfluence) ∧
  AdmitsCriterion (fun acquire => (observe acquire, acquire)) ReviewInfluence ∧
  (∀ (acquire : Acquisition) review external reason, run acquire review external reason true = true)

end TruthCore.Modal.ReasonResponseHistory
