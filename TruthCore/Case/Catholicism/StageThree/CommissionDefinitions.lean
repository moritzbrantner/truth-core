module

public import TruthCore.Case.Catholicism.StageThree.Commissions
public import TruthCore.Logic.ExcludedMiddle

/-!
# Governing-power criteria and the matching institutional bridge

The old nine-power vocabulary and Power.Governing table remain fixed. They
exclude teaching from the governing classification. A selected criterion can
instead include teaching, or have another extension. These are analyst
calibrations on the existing nine powers, not a census of all real forms of
power or an attribution to a council. Teaching may be a practice of conveying
content or an exercise of an institution's authority; the criterion and the
institutional bridge must be specified together. Classifying a power alone
neither establishes its grant nor makes a society founded in a mandate.

The old bridge quantifies over its fixed narrow table. It cannot be reused at
a broader criterion merely by changing the word governing. Matthew 28 going
back to Jesus is an explicit historical premise, not its literal textual report.
Gave retains the existing gave-or-promised reading and recipient limitations;
no actual institutional authority or fulfilled promise is independently proved.
-/

@[expose] public section

namespace TruthCore.Case.Catholicism.StageThree.CommissionDefinitions

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism.StageThree.Commissions

/-- Open calibration against the unchanged fixed table. -/
def NarrowGovernanceCriterion (governing : Power → Prop) : Prop :=
  ∀ p, governing p ↔ p.Governing = true

/-- Open alternative including teaching; its institutional applicability is
not supplied merely by this criterion. -/
def TeachingInclusiveGovernanceCriterion (governing : Power → Prop) : Prop :=
  ∀ p, governing p ↔ p.Governing = true ∨ p = .teach

/-- Open coverage of two named extensions on the nine-power carrier. -/
def NamedGovernanceCoverage (governing : Power → Prop) : Prop :=
  NarrowGovernanceCriterion governing ∨ TeachingInclusiveGovernanceCriterion governing

/-- A genuinely different criterion, e.g. one adding baptizing to the narrow
table without adding teaching. No new identifier counts as an extra option. -/
def AdditionalGovernanceCriterion (governing : Power → Prop) : Prop :=
  ¬ NarrowGovernanceCriterion governing ∧ ¬ TeachingInclusiveGovernanceCriterion governing

/-- Logical coverage with a further criterion retained. -/
def GovernanceCriterionCases (governing : Power → Prop) : Prop :=
  NarrowGovernanceCriterion governing ∨ TeachingInclusiveGovernanceCriterion governing ∨
    AdditionalGovernanceCriterion governing

/-- Actual negation of the narrow calibration, not its inadequacy for a target. -/
def NarrowGovernanceCriterionFails (governing : Power → Prop) : Prop :=
  ¬ NarrowGovernanceCriterion governing

/-- The matching institutional bridge, preserving mandate/body/teaching scope
of the original while making the governing criterion a visible parameter. -/
def InstitutionLinkFor (σ : Signature) (A : Agency σ) (E : Commissioning)
    (governing : Power → Prop) : Prop :=
  ∀ g, A.HoldsMandate σ.jesus g →
    σ.Founded σ.jesus σ.catholicChurch → σ.VisibleWithAuthority σ.catholicChurch →
      (∀ p, governing p → E.Gave p → A.FoundedInMandate σ.jesus g σ.catholicChurch) ∧
      (E.Gave .teach → A.CommissionedToTeach σ.jesus σ.catholicChurch)

/-- A literal fixed teaching-inclusive link is stronger than the old narrow
link. This is not an automatic transfer from that old link. -/
def TeachingInclusiveInstitutionLink (σ : Signature) (A : Agency σ)
    (E : Commissioning) : Prop :=
  InstitutionLinkFor σ A E (fun p => p.Governing = true ∨ p = .teach)

/-- The Matthew 28 commission actually goes back to Jesus in the existing
gave-or-promised sense. The report by itself does not establish this premise. -/
def Matthew28GoesBack (E : Commissioning) : Prop :=
  GoesBackToJesus E .mt28

/-- Exact equivalence between old and parameterized bridges under the narrow
calibration; no dictionary identification is hidden. -/
def NarrowInstitutionCalibration (σ : Signature) (A : Agency σ)
    (E : Commissioning) (governing : Power → Prop) : Prop :=
  ChurchFoundedInCommissionedApostles σ A E ↔ InstitutionLinkFor σ A E governing

/-- Four controls: old narrow link true/broader link false in the original
nonempty message model; consistent teaching-inclusive premises; and further
criteria admitting or denying the old mandate target. Schema interpretations
only, with no source, historical or actual institutional truth asserted. -/
def CommissionCriterionModels : Prop :=
  (∃ σ : Signature, ∃ A : Agency σ, ∃ E : Commissioning,
    ChurchFoundedInCommissionedApostles σ A E ∧ MandateCoversOnlyMessage σ A ∧
    (∃ g, A.HoldsMandate σ.jesus g) ∧ σ.Founded σ.jesus σ.catholicChurch ∧
    σ.VisibleWithAuthority σ.catholicChurch ∧ Matthew28GoesBack E ∧
    ¬ TeachingInclusiveInstitutionLink σ A E) ∧
  (∃ σ : Signature, ∃ A : Agency σ, ∃ E : Commissioning, ∃ governing : Power → Prop,
    TeachingInclusiveGovernanceCriterion governing ∧ InstitutionLinkFor σ A E governing ∧
    Matthew28GoesBack E ∧ (∃ g, A.HoldsMandate σ.jesus g) ∧
    σ.Founded σ.jesus σ.catholicChurch ∧ σ.VisibleWithAuthority σ.catholicChurch ∧
    MandatedFoundingOfCatholicChurch σ A) ∧
  (∃ σ : Signature, ∃ A : Agency σ, ∃ E : Commissioning, ∃ governing : Power → Prop,
    AdditionalGovernanceCriterion governing ∧ InstitutionLinkFor σ A E governing ∧
    Matthew28GoesBack E ∧ (∃ g, A.HoldsMandate σ.jesus g) ∧
    σ.Founded σ.jesus σ.catholicChurch ∧ σ.VisibleWithAuthority σ.catholicChurch ∧
    MandatedFoundingOfCatholicChurch σ A) ∧
  (∃ σ : Signature, ∃ A : Agency σ, ∃ E : Commissioning, ∃ governing : Power → Prop,
    AdditionalGovernanceCriterion governing ∧ InstitutionLinkFor σ A E governing ∧
    Matthew28GoesBack E ∧ (∃ g, A.HoldsMandate σ.jesus g) ∧
    σ.Founded σ.jesus σ.catholicChurch ∧ σ.VisibleWithAuthority σ.catholicChurch ∧
    ¬ MandatedFoundingOfCatholicChurch σ A)

end TruthCore.Case.Catholicism.StageThree.CommissionDefinitions
