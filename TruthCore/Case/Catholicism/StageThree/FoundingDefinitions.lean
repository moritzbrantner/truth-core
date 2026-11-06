module

public import TruthCore.Case.Catholicism.StageThree.DivineFounding
public import TruthCore.Logic.ExcludedMiddle

/-!
# Competing meanings of divine founding

The existing signature's `FoundedAsTeachingAuthority` stays independent. A
supplied `direct` relation records founding by the principal's own constitutive
act, rather than identifying it with every authorized act of an envoy. For an
ordinary agency analogy, a principal can issue a charter personally, or an
authorized representative can issue it in the principal's name. These are not
made equivalent. Both acts can contribute to one society, so their extensions
need not be disjoint. Whether that analogy applies to divine founding remains
open; no event in Christian history is established by this profile.

Two explicit definition propositions compare the existing target predicate
with (a) direct founding alone and (b) direct founding or the existing Jesus-
envoy teaching event. They constrain only beings satisfying `IsGod`, which is
the exact scope the existing envoy bridge needs. The meaning of other beings'
founding remains unrestricted. Neither proposition asserts that a mandate is
held: the existing `FoundedInMandate` and `HoldsMandate` are separate fields.

Named coverage is an open framework premise. Coverage with an explicit further
reading follows from excluded middle; it does not prove that the named pair
exhausts the actual meanings. The alternatives can overlap extensionally.
-/

@[expose] public section

namespace TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding

/-- The exact existing envoy event; holding a mandate is not silently added. -/
def EnvoyTeachingEvent (σ : Signature) (A : Agency σ) (g : σ.Being)
    (c : σ.Society) : Prop :=
  A.FoundedInMandate σ.jesus g c ∧ A.CommissionedToTeach σ.jesus c

/-- Open immediate-only definition proposition, on God candidates only. -/
def ImmediateOnlyReading (σ : Signature) (_A : Agency σ)
    (direct : σ.Being → σ.Society → Prop) : Prop :=
  ∀ g c, σ.IsGod g → (σ.FoundedAsTeachingAuthority g c ↔ direct g c)

/-- Open envoy-inclusive definition proposition. Other envoys are not included
by the Jesus-specific event. Direct founding is admitted as a separate case. -/
def EnvoyInclusiveReading (σ : Signature) (A : Agency σ)
    (direct : σ.Being → σ.Society → Prop) : Prop :=
  ∀ g c, σ.IsGod g →
    (σ.FoundedAsTeachingAuthority g c ↔ direct g c ∨ EnvoyTeachingEvent σ A g c)

/-- Named semantic coverage for this fixed target predicate, agency profile
and direct-founding relation. This is not a census of historical schools. -/
def NamedReadingCoverage (σ : Signature) (A : Agency σ)
    (direct : σ.Being → σ.Society → Prop) : Prop :=
  ImmediateOnlyReading σ A direct ∨ EnvoyInclusiveReading σ A direct

/-- The fixed target predicate coextends with neither named reading. Its
extension, not its spelling or identifier, differs from both candidates. -/
def AdditionalFoundingReading (σ : Signature) (A : Agency σ)
    (direct : σ.Being → σ.Society → Prop) : Prop :=
  ¬ ImmediateOnlyReading σ A direct ∧ ¬ EnvoyInclusiveReading σ A direct

/-- A checked logical fork with the remaining option explicit. -/
def ReadingCoverageWithRemainder (σ : Signature) (A : Agency σ)
    (direct : σ.Being → σ.Society → Prop) : Prop :=
  ImmediateOnlyReading σ A direct ∨ EnvoyInclusiveReading σ A direct ∨
    AdditionalFoundingReading σ A direct

/-- One candidate is eliminated for this fixed semantic profile, rather than
ruled out universally or rejected merely because it is not preferred. -/
def ImmediateReadingFails (σ : Signature) (A : Agency σ)
    (direct : σ.Being → σ.Society → Prop) : Prop :=
  ¬ ImmediateOnlyReading σ A direct

/-- Under the immediate-only reading, the envoy bridge requires this additional
compatibility condition; immediate-only does not by itself make it false. -/
def ImmediateAdmitsEnvoy (σ : Signature) (A : Agency σ)
    (direct : σ.Being → σ.Society → Prop) : Prop :=
  ∀ g c, σ.IsGod g → EnvoyTeachingEvent σ A g c → direct g c

/-- An explicit extra exclusion for this Jesus-specific comparison. This is
not derived from directness or from Jesus being distinct from a God candidate;
no such identity condition is encoded. It is weaker in scope than excluding
every possible creature's constitutive act, and can be rejected separately. -/
def DirectExcludesJesusEnvoy (σ : Signature) (A : Agency σ)
    (direct : σ.Being → σ.Society → Prop) : Prop :=
  ∀ g c, σ.IsGod g → EnvoyTeachingEvent σ A g c → ¬ direct g c

/-- Strong sibling: the target accepts the direct criterion and no direct
founding in this God-society scope is also a Jesus-envoy teaching event. -/
def ExclusiveImmediateReading (σ : Signature) (A : Agency σ)
    (direct : σ.Being → σ.Society → Prop) : Prop :=
  ImmediateOnlyReading σ A direct ∧ DirectExcludesJesusEnvoy σ A direct

/-- Negation of the existing envoy bridge, not a rejection of the root. -/
def EnvoyBridgeFails (σ : Signature) (A : Agency σ) : Prop :=
  ¬ EnvoyFoundingIsPrincipalsFounding σ A

/-- Exact calibration of the old bridge under the immediate-only meaning. -/
def ImmediateEnvoyCalibration (σ : Signature) (A : Agency σ)
    (direct : σ.Being → σ.Society → Prop) : Prop :=
  EnvoyFoundingIsPrincipalsFounding σ A ↔ ImmediateAdmitsEnvoy σ A direct

/-- Root-bridge antecedents, reused unchanged from the original schema model. -/
def StageAntecedents (σ : Signature) : Prop :=
  GodExists σ.IsGod ∧ GodHasClassicalAttributes σ ∧
  RevelationPossibleAndRecognizable σ ∧ JesusClaimedDivineAuthorityAndRose σ ∧
  ChristFoundedVisibleChurch σ

/-- A nonempty commissioned-event witness on an actual God candidate. -/
def EnvoyEventExists (σ : Signature) (A : Agency σ) : Prop :=
  ∃ g c, σ.IsGod g ∧ EnvoyTeachingEvent σ A g c

/-- Five finite interpretation controls. Both named readings can coincide;
each can hold without the other; further readings can admit or reject the old
envoy bridge. These certify only the explicitly listed formal conditions. -/
def DefinitionModels : Prop :=
  (∃ σ : Signature, ∃ A : Agency σ, ∃ direct : σ.Being → σ.Society → Prop,
    StageAntecedents σ ∧ EnvoyEventExists σ A ∧
    ImmediateOnlyReading σ A direct ∧ EnvoyInclusiveReading σ A direct ∧
    EnvoyFoundingIsPrincipalsFounding σ A) ∧
  (∃ σ : Signature, ∃ A : Agency σ, ∃ direct : σ.Being → σ.Society → Prop,
    StageAntecedents σ ∧ EnvoyEventExists σ A ∧
    ImmediateOnlyReading σ A direct ∧ ¬ EnvoyInclusiveReading σ A direct ∧
    ¬ EnvoyFoundingIsPrincipalsFounding σ A ∧ ¬ BridgeChristsChurchFoundedByGod σ) ∧
  (∃ σ : Signature, ∃ A : Agency σ, ∃ direct : σ.Being → σ.Society → Prop,
    StageAntecedents σ ∧ EnvoyEventExists σ A ∧
    EnvoyInclusiveReading σ A direct ∧ ¬ ImmediateOnlyReading σ A direct ∧
    EnvoyFoundingIsPrincipalsFounding σ A) ∧
  (∃ σ : Signature, ∃ A : Agency σ, ∃ direct : σ.Being → σ.Society → Prop,
    StageAntecedents σ ∧ AdditionalFoundingReading σ A direct ∧
    EnvoyFoundingIsPrincipalsFounding σ A) ∧
  (∃ σ : Signature, ∃ A : Agency σ, ∃ direct : σ.Being → σ.Society → Prop,
    StageAntecedents σ ∧ EnvoyEventExists σ A ∧
    AdditionalFoundingReading σ A direct ∧ ¬ EnvoyFoundingIsPrincipalsFounding σ A)

end TruthCore.Case.Catholicism.StageThree.FoundingDefinitions
