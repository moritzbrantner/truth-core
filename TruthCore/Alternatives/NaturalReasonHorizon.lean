module

public import TruthCore.Alternatives.Fideism
public import TruthCore.Logic.ExcludedMiddle

/-!
# Natural reason: shared standards and theological audiences

The existing shared-reason bridge concerns whether natural-knowability moves
answer to outsider-shared standards. A description of their users as theists
and their endorsement by a practice's own standards is different. A person can
stand outside one religious practice while remaining a theist; availability
without that practice's authority is not neutrality to every worldview.

The typed audience profile below does not define universal worldview neutrality
or establish actual apologetic history. It records a modest descriptive horizon
sibling. The earlier mixed prose reconstruction remains unchanged. In contrast,
the all-nonshared proposition is an exact rival to the shared bridge only with
an actual natural-knowability move. Mixed witnesses supply a further profile
that neither uniform interpretation covers. Named uniform coverage stays open.
-/

@[expose] public section

namespace TruthCore.Alternatives.NaturalReasonHorizon

open TruthCore.Alternatives.Fideism

/-- Users and practice membership, not a claim that nonmembers reject theism. -/
structure Audience (P : Practice) where
  Agent : Type
  InPractice : Agent → Prop
  Theistic : Agent → Prop
  UsesMove : Agent → P.Move → Prop

/-- Modest descriptive horizon: natural-knowability users are theists and the
practice's own standards endorse these moves. This does not exclude sharedness. -/
def DescriptiveTheisticHorizon (P : Practice) (A : Audience P) : Prop :=
  (∀ a m, P.AffirmsNaturalKnowability m → A.UsesMove a m → A.Theistic a) ∧
  (∀ m, P.AffirmsNaturalKnowability m → P.OwnStandard m)

/-- An actual nonmember uses a natural-knowability move; a nonmember may still
be a theist. This says nothing about every possible worldview's standards. -/
def OutsiderNaturalUseExists (P : Practice) (A : Audience P) : Prop :=
  ∃ a m, ¬ A.InPractice a ∧ A.UsesMove a m ∧ P.AffirmsNaturalKnowability m

/-- Weak actual-move witness. Unlike the council premise, no Defined property
is assumed; it suffices for comparing the two universal bridge readings. -/
def NaturalKnowabilityMoveExists (P : Practice) : Prop :=
  ∃ m, P.AffirmsNaturalKnowability m

/-- Every natural-knowability move lacks the selected shared-reason property.
No positive claim that it is correct or endorsed internally is added. -/
def NaturalReasonNeverShared (P : Practice) : Prop :=
  ∀ m, P.AffirmsNaturalKnowability m → ¬ P.AnswersToSharedReason m

/-- A precise additional relevant profile: one natural-knowability move is
shared and another is not. The two universal readings both fail here. -/
def MixedNaturalReason (P : Practice) : Prop :=
  (∃ m, P.AffirmsNaturalKnowability m ∧ P.AnswersToSharedReason m) ∧
  (∃ m, P.AffirmsNaturalKnowability m ∧ ¬ P.AnswersToSharedReason m)

/-- Open named uniform-profile coverage; mixed behavior is not ignored. -/
def NamedNaturalReasonCoverage (P : Practice) : Prop :=
  NaturalReasonIsSharedReading P ∨ NaturalReasonNeverShared P

/-- Structural shared/nonshared/mixed coverage, using explicit EM. Without an
actual natural move the first two cases can both hold vacuously. -/
def NaturalReasonProfileCases (P : Practice) : Prop :=
  NaturalReasonIsSharedReading P ∨ NaturalReasonNeverShared P ∨ MixedNaturalReason P

/-- Exact negation of the existing shared-reason interpretation bridge. -/
def SharedNaturalReasonRejected (P : Practice) : Prop :=
  ¬ NaturalReasonIsSharedReading P

/-- Both universal interpretations fail; not a rejection of the descriptive
horizon, natural knowledge itself, or a whole worldview. -/
def UniformNaturalReasonRejected (P : Practice) : Prop :=
  ¬ NaturalReasonIsSharedReading P ∧ ¬ NaturalReasonNeverShared P

/-- Four controls: a descriptive theological audience with either shared or
nonshared standards; an actual mixed profile; and empty-natural-move overlap.
These certify interpretations only, not real apologetic or religious history. -/
def HorizonModels : Prop :=
  (∃ P : Practice, ∃ A : Audience P,
    DescriptiveTheisticHorizon P A ∧ OutsiderNaturalUseExists P A ∧
    NaturalKnowabilityMoveExists P ∧ NaturalReasonIsSharedReading P ∧
    ¬ NaturalReasonNeverShared P) ∧
  (∃ P : Practice, ∃ A : Audience P,
    DescriptiveTheisticHorizon P A ∧ OutsiderNaturalUseExists P A ∧
    NaturalKnowabilityMoveExists P ∧ NaturalReasonNeverShared P ∧
    ¬ NaturalReasonIsSharedReading P) ∧
  (∃ P : Practice, ∃ A : Audience P,
    DescriptiveTheisticHorizon P A ∧ OutsiderNaturalUseExists P A ∧
    MixedNaturalReason P ∧ UniformNaturalReasonRejected P) ∧
  (∃ P : Practice,
    ¬ NaturalKnowabilityMoveExists P ∧ NaturalReasonIsSharedReading P ∧
    NaturalReasonNeverShared P)

end TruthCore.Alternatives.NaturalReasonHorizon
