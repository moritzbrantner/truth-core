module

public import TruthCore.Case.Catholicism.StageThree.Commissions
public import TruthCore.Logic.ExcludedMiddle

/-! The message-only mandate thesis concerns institutional founding, not
whether reports describe actual grants or promises of powers. Keep the fixed
nine-power table and gave-or-promised reading. The institutional transfer and
actual mandate/body witnesses are separate inputs. No historical or source
claim is strengthened; these are analyst boundary propositions. -/
@[expose] public section
namespace TruthCore.Case.Catholicism.StageThree.MessageReportBoundary
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism.StageThree.Commissions

/-- Only the governing-event-to-mandate-founding component of the old link.
The teaching-commission component is unnecessary to confront message-only. -/
def GoverningEventInstitutionLink (σ : Signature) (A : Agency σ)
    (E : Commissioning) : Prop :=
  ∀ g, A.HoldsMandate σ.jesus g → σ.Founded σ.jesus σ.catholicChurch →
    σ.VisibleWithAuthority σ.catholicChurch →
    (∃ p, p.Governing = true ∧ E.Gave p) →
      A.FoundedInMandate σ.jesus g σ.catholicChurch

/-- An actual mandate and actual founding/visibility of the selected body.
Neither a literal report nor an empty universal mandate supplies this. -/
def ActualMandatedCatholicFounding (σ : Signature) (A : Agency σ) : Prop :=
  ∃ g, A.HoldsMandate σ.jesus g ∧ σ.Founded σ.jesus σ.catholicChurch ∧
    σ.VisibleWithAuthority σ.catholicChurch

def GoverningGrantExists (E : Commissioning) : Prop :=
  ∃ p, p.Governing = true ∧ E.Gave p

def NoGoverningGrant (E : Commissioning) : Prop :=
  ∀ p, p.Governing = true → ¬ E.Gave p

/-- Exact negation of the existing report-to-event bundle; not merely lack of
institutional founding and not a denial of the literal reports. -/
def HistoricalCommissionBundleRejected (E : Commissioning) : Prop :=
  ¬ CommissionReportsGoBackToJesus E

/-- Precise positive remainder: the institutional transfer fails at an actual
mandate/body with an actual governing grant, without mandate-founding. -/
def InstitutionalTransferCountercase (σ : Signature) (A : Agency σ)
    (E : Commissioning) : Prop :=
  ∃ g, A.HoldsMandate σ.jesus g ∧ σ.Founded σ.jesus σ.catholicChurch ∧
    σ.VisibleWithAuthority σ.catholicChurch ∧ GoverningGrantExists E ∧
    ¬ A.FoundedInMandate σ.jesus g σ.catholicChurch

def InstitutionalTransferCases (σ : Signature) (A : Agency σ)
    (E : Commissioning) : Prop :=
  GoverningEventInstitutionLink σ A E ∨ InstitutionalTransferCountercase σ A E

/-- A nonempty coexistence model of the raw rival and full historical bundle,
and the older nonempty Matthew28 concession with the old link. -/
def MessageReportModels : Prop :=
  (∃ σ : Signature, ∃ A : Agency σ, ∃ E : Commissioning,
    MandateCoversOnlyMessage σ A ∧ CommissionReportsGoBackToJesus E ∧
    ActualMandatedCatholicFounding σ A ∧ InstitutionalTransferCountercase σ A E ∧
    ¬ GoverningEventInstitutionLink σ A E) ∧
  (∃ σ : Signature, ∃ A : Agency σ, ∃ E : Commissioning,
    MandateCoversOnlyMessage σ A ∧ ChurchFoundedInCommissionedApostles σ A E ∧
    ActualMandatedCatholicFounding σ A ∧ GoesBackToJesus E .mt28 ∧
    NoGoverningGrant E ∧ HistoricalCommissionBundleRejected E)
/-- Exact negation of the conditional Catholic-only mandate scope. The raw
message thesis implies this only with an actual mandate and founded body. -/
def CatholicMandateScopeRejected (σ : Signature) (A : Agency σ) : Prop :=
  ¬ MandatedFoundingOfCatholicChurch σ A

/-- An unrealized combined mandate/body antecedent permits the two raw
conditionals to coexist; actual joint witnesses make their opposition
nonvacuous. This coarse target does not export which antecedent is absent. -/
def MessageScopeModels : Prop :=
  (∃ σ : Signature, ∃ A : Agency σ,
    MandateCoversOnlyMessage σ A ∧ MandatedFoundingOfCatholicChurch σ A ∧
    ¬ ActualMandatedCatholicFounding σ A) ∧
  (∃ σ : Signature, ∃ A : Agency σ,
    MandateCoversOnlyMessage σ A ∧ ActualMandatedCatholicFounding σ A ∧
    CatholicMandateScopeRejected σ A)

/-- The old narrow-scope conclusion retains two teaching requirements that
neither governing-only projection supplies. All mandate/body witnesses remain
actual and nonempty in these omission controls. -/
def GoverningComponentsDoNotForceTeachingScope : Prop :=
  (∃ σ : Signature, ∃ A : Agency σ, ∃ E : Commissioning,
    GoverningEventInstitutionLink σ A E ∧ CommissionReportsGoBackToJesus E ∧
    ActualMandatedCatholicFounding σ A ∧ ¬ MandatedFoundingOfCatholicChurch σ A) ∧
  (∃ σ : Signature, ∃ A : Agency σ, ∃ E : Commissioning,
    ChurchFoundedInCommissionedApostles σ A E ∧ GoverningGrantExists E ∧
    ActualMandatedCatholicFounding σ A ∧ ¬ MandatedFoundingOfCatholicChurch σ A)
/-- The stronger empty-mandate control explicitly exports absence of every
Jesus mandate while retaining an actual founded visible Catholic body. Unlike the
coarser MessageScopeModels target, no consumer must inspect the construction
to distinguish lack of mandate from lack of founding or visibility. -/
def EmptyMandateScopeCoexistence : Prop :=
  ∃ σ : Signature, ∃ A : Agency σ,
    MandateCoversOnlyMessage σ A ∧ MandatedFoundingOfCatholicChurch σ A ∧
    (∀ g, ¬ A.HoldsMandate σ.jesus g) ∧
    σ.Founded σ.jesus σ.catholicChurch ∧ σ.VisibleWithAuthority σ.catholicChurch
end TruthCore.Case.Catholicism.StageThree.MessageReportBoundary
