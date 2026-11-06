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
end TruthCore.Case.Catholicism.StageThree.FoundingWeakScope
