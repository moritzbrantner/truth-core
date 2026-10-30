import TruthCore.Science.MeasurementCalibration
import TruthCore.Logic.CorrectionCriterion

/-! Analyst's composition of the additive calibration model and the exact
data-relative criterion. Accuracy here means zero constant offset, not every
kind of instrument accuracy or epistemic justification. The signal functions
are unrestricted; compensating shifts therefore remain in the model class.
Reports may have any type, including an infinite sequence, but are functions
only of the original complete readings. No claim is attributed to Duhem,
Wittgenstein, Goldman or an infinitist by this mathematical composition. -/
namespace TruthCore.Science.ReadingSelfCertification

/-- Packaging the signal and constant offset already used by
`MeasurementCalibration`; this adds no instrument ontology. -/
abbrev Profile (X V : Type) := (X → V) × V

/-- All exact readings, not merely a finite sample. -/
def readings {X V : Type} [Add V] (p : Profile X V) : X → V :=
  fun x => p.1 x + p.2

/-- Offset accuracy in this idealized profile: the constant bias is zero.
This is not a definition of warranted belief or reliable belief formation. -/
def Accurate {X V : Type} [Zero V] (p : Profile X V) : Prop := p.2 = 0

/-- In addition to the readings, supply the true signal value at one input.
Neither availability nor warrant for that additional datum is asserted. -/
def anchoredReadings {X V : Type} [Add V] (x₀ : X) (p : Profile X V) :
    (X → V) × V := (readings p, p.1 x₀)

/-- Any reading-derived positive certificate that uniformly guarantees zero
bias must withhold affirmation on every reachable datum. A permitted nonzero
offset is explicit. No finite or inhabited input assumption is needed for
this universal obstruction; the concrete control below is inhabited and has
two unequal readings. An arbitrary report type includes `Nat → Report`, but
the reports must still be derived from these same readings. -/
def SoundSelfCertificationFails : Prop :=
  ∀ (X V : Type) [AddCommGroup V] (d : V), d ≠ 0 →
    ∀ (Evidence : Type) (derive : (X → V) → Evidence) (test : Evidence → Prop),
      (∀ p : Profile X V, test (derive (readings p)) → Accurate p) →
      ∀ p : Profile X V, ¬ test (derive (readings p))

/-- In particular, no exact classifier for accuracy is available from any
such derived reports. This uses the existing generic criterion meaning. -/
def ExactSelfCertificationFails : Prop :=
  ∀ (X V : Type) [AddCommGroup V] (d : V), d ≠ 0 →
    ∀ (Evidence : Type) (derive : (X → V) → Evidence),
      ¬ TruthCore.Logic.CorrectionCriterion.AdmitsCriterion
        (fun p : Profile X V => derive (readings p)) Accurate

/-- A supplied true signal anchor permits an exact extensional criterion in
the constant-bias model. This is an information boundary, not a proof of the
anchor's independent epistemic entitlement. -/
def AnchorAllowsCriterion : Prop :=
  ∀ (X V : Type) [AddCommGroup V] (x₀ : X),
    TruthCore.Logic.CorrectionCriterion.AdmitsCriterion
      (anchoredReadings (V := V) x₀) Accurate

/-- A nonconstant two-input integer witness has the same complete readings
with zero and nonzero bias. Its supplied true signal anchors differ. -/
def SelfCertificationControl : Prop :=
  ∃ p q : Profile Bool Int,
    readings p = readings q ∧ Accurate p ∧ ¬ Accurate q ∧
    readings p false ≠ readings p true ∧
    (∀ x, p.1 x ≠ q.1 x) ∧
    anchoredReadings false p ≠ anchoredReadings false q

/-- Uniform soundness obstruction, exact-criterion obstruction, supplied-
anchor survivor, and a nondegenerate joint witness. -/
def Certificate : Prop :=
  SoundSelfCertificationFails ∧ ExactSelfCertificationFails ∧
    AnchorAllowsCriterion ∧ SelfCertificationControl

end TruthCore.Science.ReadingSelfCertification
