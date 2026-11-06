module

public import TruthCore.Case.Catholicism.StageThree.FoundingScope

/-! A schema counterinterpretation of replacing the universal mandate scope by
its Catholic-Church-only instance in the four-input divine-founding bridge.
Both scopes retain teaching. Only the range of societies differs. This does
not model actual Christian history or refute the universal scope premise. -/
@[expose] public section
namespace TruthCore.Case.Catholicism.StageThree.FoundingWeakScope
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope

/-- Reuse the two-society model, changing only divine teaching-founding: it
holds at the Catholic society, whereas Jesus founded both visible societies. -/
def restrictedSig : Signature :=
  { twoSocietySig with FoundedAsTeachingAuthority := fun _ c => c = true }

/-- Same agency interpretation as twoSocietyAgency, on the restricted
signature: attestation is truth, the mandate is held, and founding in mandate
and teaching commission hold exactly at the Catholic society. -/
def restrictedAgency : Agency restrictedSig where
  Confirms := twoSocietyAgency.Confirms
  HoldsMandate := twoSocietyAgency.HoldsMandate
  FoundedInMandate := twoSocietyAgency.FoundedInMandate
  CommissionedToTeach := twoSocietyAgency.CommissionedToTeach

/-- All bridge antecedents are inhabited, and attestation, veracity, the weak
scope and envoy transfer hold, while the universal divine-founding bridge
fails. Universal mandate scope and stage6 identity also fail: the witness is
not a countermodel to the existing weak-scope-plus-stage6 composition. -/
def WeakScopeDoesNotForceBridge : Prop :=
  ∃ σ : Signature, ∃ A : Agency σ,
    GodExists σ.IsGod ∧ GodHasClassicalAttributes σ ∧
    RevelationPossibleAndRecognizable σ ∧ JesusClaimedDivineAuthorityAndRose σ ∧
    ChristFoundedVisibleChurch σ ∧ ResurrectionConfirmsMandate σ A ∧
    GodConfirmsOnlyTruth σ A ∧ MandatedFoundingOfCatholicChurch σ A ∧
    EnvoyFoundingIsPrincipalsFounding σ A ∧
    ¬ BridgeChristsChurchFoundedByGod σ ∧
    ¬ MandatedFoundingWithTeaching σ A ∧ ¬ ChristsChurchIsCatholicChurch σ
/-- Stronger export for the same scope counterexample: the weak Catholic
instance is actually triggered at the God witness, and a distinct other body
is actually founded and visible. Divine teaching-founding fails at that very
other body. No consumer must infer these fields from the hidden witness term. -/
def ExplicitBodiesScopeCountermodel : Prop :=
  ∃ σ : Signature, ∃ A : Agency σ, ∃ g : σ.Being, ∃ c : σ.Society,
    GodExists σ.IsGod ∧ GodHasClassicalAttributes σ ∧
    RevelationPossibleAndRecognizable σ ∧ JesusClaimedDivineAuthorityAndRose σ ∧
    ChristFoundedVisibleChurch σ ∧ ResurrectionConfirmsMandate σ A ∧
    GodConfirmsOnlyTruth σ A ∧ MandatedFoundingOfCatholicChurch σ A ∧
    EnvoyFoundingIsPrincipalsFounding σ A ∧ σ.IsGod g ∧
    A.HoldsMandate σ.jesus g ∧
    σ.Founded σ.jesus σ.catholicChurch ∧ σ.VisibleWithAuthority σ.catholicChurch ∧
    c ≠ σ.catholicChurch ∧ σ.Founded σ.jesus c ∧ σ.VisibleWithAuthority c ∧
    ¬ σ.FoundedAsTeachingAuthority g c ∧
    ¬ BridgeChristsChurchFoundedByGod σ ∧
    ¬ MandatedFoundingWithTeaching σ A ∧ ¬ ChristsChurchIsCatholicChurch σ
end TruthCore.Case.Catholicism.StageThree.FoundingWeakScope
