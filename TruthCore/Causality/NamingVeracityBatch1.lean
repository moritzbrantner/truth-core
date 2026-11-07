module

public import TruthCore.Case.Catholicism.StageThree.DivineFounding
public import TruthCore.Case.Catholicism.StageTwo

/-! Naming, veracity, revelation and authority: batch 1 (exploration maps
`explorations/god-names-fully-described.toml`, `god-confirms-only-truth.toml`,
`revelation-possible.toml`, `god-founded-authority-truth.toml`).

Analyst formulations, attribution deferred (owner direction 2026-11-05). Each
definition below is an OPEN premise or an intermediate node; none is attributed
to a source. Where a pinned claim bears on a node, the corpus records a
`supports` relation, never a stating claim.

The stage-3 nodes are typed over the skeleton `Signature` and the
`DivineFounding.Agency` vocabulary, so the derivations bind to the existing
statements `STMT-GOD-CONFIRMS-ONLY-TRUTH`,
`STMT-BRIDGE-GOD-FOUNDED-AUTHORITY-PROPOSES-ONLY-TRUTH` and
`STMT-REVELATION-POSSIBLE-AND-RECOGNIZABLE` exactly. Three small vocabulary
structures are added as parameters with no axioms: `Veracity` (asserting,
believing, knowing), `Assistance` (a founder's assistance of a society) and
`Power` (tasks, their consistency, and who can do them). -/

@[expose] public section

namespace TruthCore.Causality.NamingVeracityBatch1

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Latin.Aquinas.SummaTheologiae (IsMaximumIn CausesAllInGenus)

/-! ## Naming (q.2 a.3, q.13 a.8) -/

/-- OPEN analyst bridge (map node `NEW-NAME-GOD-IMPOSED-FROM-OPERATION`): the
name "God" is imposed from the universal causality attributed to its bearer
(q.13 a.8: *imponitur ab operatione*), so it applies to whatever is the only
cause of the being of every other being. Uniqueness is read, as in the naming
leaves, as a definite-description condition of application. Only causation of
being is kept; providence is not encoded. -/
def NameGodImposedFromOperation {B R : Type} (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) (God : B → Prop) : Prop :=
  ∀ m, CausesAllInGenus InAct CausesIn esse m →
    (∀ m', CausesAllInGenus InAct CausesIn esse m' → m' = m) → God m

/-- OPEN analyst bridge (map node `NEW-UNIVERSAL-CAUSE-OF-BEING-IS-MAXIMAL`):
whatever causes the being of every other being is maximal in being (it has
being and nothing is more a being than it). The converse direction of the
*quarta via*'s "the maximum in a genus is the cause of all in it"; not stated
by the source. -/
def UniversalCauseOfBeingIsMaximal {B R : Type} (InAct : B → R → Prop)
    (MoreIn : R → B → B → Prop) (CausesIn : B → B → R → Prop) (esse : R) : Prop :=
  ∀ m, CausesAllInGenus InAct CausesIn esse m → IsMaximumIn InAct MoreIn esse m

/-! ## Veracity -/

/-- Cognitive and assertoric vocabulary over the skeleton signature.

* `Asserts g p` — `g` asserts `p` (puts `p` forward as true, on `g`'s own word).
* `Believes g p` — `g` assents to `p`.
* `Knows g p` — `g` holds `p` as known. Factivity is **not** built in: that what
  God knows is true is the separate premise `GodKnowsOnlyTruths`.

All three are uninterpreted parameters. -/
structure Veracity (σ : Signature) where
  Asserts : σ.Being → Prop → Prop
  Believes : σ.Being → Prop → Prop
  Knows : σ.Being → Prop → Prop

/-- OPEN analyst bridge (`NEW-CONFIRMING-IS-ASSERTING`): whoever confirms a
proposition by a sign asserts it. A sign given as confirmation is testimonial
(DEF-FOUNDED-BY-GOD-THROUGH-ENVOY), so it carries the confirmer's word. -/
def ConfirmingIsAsserting (σ : Signature) (A : Agency σ) (V : Veracity σ) : Prop :=
  ∀ g (p : Prop), A.Confirms g p → V.Asserts g p

/-- OPEN (`NEW-GOD-ASSERTS-ONLY-WHAT-HE-KNOWS`): a God with the classical
attributes asserts only what he holds as known (sincerity: no deception). -/
def GodAssertsOnlyWhatHeKnows (σ : Signature) (V : Veracity σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ p : Prop, V.Asserts g p → V.Knows g p

/-- OPEN (`NEW-GOD-KNOWS-ONLY-TRUTHS`): what a God with the classical attributes
holds as known is true (infallibility: he is not deceived). -/
def GodKnowsOnlyTruths (σ : Signature) (V : Veracity σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → ∀ p : Prop, V.Knows g p → p

/-- OPEN analyst bridge (`NEW-CLASSICAL-ATTRIBUTES-INCLUDE-PERFECT-INTELLECT-AND-GOOD-WILL`):
whatever is God with the classical attributes asserts only what he believes
(a good will intends no deception) and believes only what he knows (a perfect
intellect holds no mere opinion). The primitive `HasClassicalAttributes` field
is not unfolded; this premise supplies the two attribute consequences. -/
def ClassicalAttributesIncludePerfectIntellectAndGoodWill (σ : Signature) (V : Veracity σ) :
    Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g →
    (∀ p : Prop, V.Asserts g p → V.Believes g p) ∧ (∀ p : Prop, V.Believes g p → V.Knows g p)

/-! ## A God-founded teaching authority -/

/-- `Assists g c`: `g` stands behind the definitive teaching of the society `c`
by assistance (the promised "I am with you", Mt 28.20, as intended reading).
An uninterpreted parameter. -/
structure Assistance (σ : Signature) where
  Assists : σ.Being → σ.Society → Prop

/-- OPEN (`NEW-FOUNDER-GUARANTEES-FOUNDED-AUTHORITY`): a God with the classical
attributes who founds a society as a teaching authority assists it. -/
def FounderGuaranteesFoundedAuthority (σ : Signature) (S : Assistance σ) : Prop :=
  ∀ g c, σ.IsGod g → σ.HasClassicalAttributes g → σ.FoundedAsTeachingAuthority g c →
    S.Assists g c

/-- OPEN (`NEW-ASSISTED-DEFINITIVE-PROPOSAL-IS-CONFIRMED`): what a society
assisted by `g` definitively proposes as revealed, `g` confirms. -/
def AssistedDefinitiveProposalIsConfirmed (σ : Signature) (A : Agency σ) (S : Assistance σ) :
    Prop :=
  ∀ g c, S.Assists g c → ∀ p : Prop, σ.DefinitivelyProposesAsRevealed c p → A.Confirms g p

/-- Intermediate (`NEW-DEFINITIVE-PROPOSAL-IS-GOD-CONFIRMED`): what a teaching
authority founded by a God with the classical attributes definitively proposes
as revealed, that God confirms. -/
def DefinitiveProposalIsGodConfirmed (σ : Signature) (A : Agency σ) : Prop :=
  ∀ g c, σ.IsGod g → σ.HasClassicalAttributes g → σ.FoundedAsTeachingAuthority g c →
    ∀ p : Prop, σ.DefinitivelyProposesAsRevealed c p → A.Confirms g p

/-! ## Revelation possible and recognizable -/

/-- Power vocabulary over the skeleton signature.

* `Task` — things that may be done; `revealWithSigns` is revealing a truth and
  accompanying it with signs.
* `Consistent t` — doing `t` involves no contradiction.
* `CanDo x t` — `x` has the active power to do `t`.
* `Perfection`, `Requires t r` — the perfections (respects of act) that doing
  `t` requires; `InAct x r` — `x` is in act in `r`; `PossibleAct r` — `r` is a
  perfection something could have (it involves no contradiction).

All fields are parameters; no axiom constrains them. -/
structure Power (σ : Signature) where
  Task : Type
  revealWithSigns : Task
  Consistent : Task → Prop
  CanDo : σ.Being → Task → Prop
  Perfection : Type
  Requires : Task → Perfection → Prop
  InAct : σ.Being → Perfection → Prop
  PossibleAct : Perfection → Prop

/-- OPEN (`NEW-INFINITE-IS-UNLIMITED-ACT`): what is infinite is in act in every
possible perfection (infinity of perfection, q.7 a.1, read as unlimited act). -/
def InfiniteIsUnlimitedAct (σ : Signature) (Infinite : σ.Being → Prop) (P : Power σ) : Prop :=
  ∀ x, Infinite x → ∀ r, P.PossibleAct r → P.InAct x r

/-- OPEN (`NEW-ACTIVE-POWER-FOLLOWS-ACT`): a being can do a task if it is in act
in every perfection the task requires (q.25 a.1: active power follows act). -/
def ActivePowerFollowsAct (σ : Signature) (P : Power σ) : Prop :=
  ∀ x t, (∀ r, P.Requires t r → P.InAct x r) → P.CanDo x t

/-- OPEN (`NEW-CONSISTENT-TASK-REQUIRES-ONLY-POSSIBLE-PERFECTIONS`): a task
involving no contradiction requires only possible perfections. -/
def ConsistentTaskRequiresOnlyPossiblePerfections (σ : Signature) (P : Power σ) : Prop :=
  ∀ t, P.Consistent t → ∀ r, P.Requires t r → P.PossibleAct r

/-- Intermediate (`NEW-INFINITE-ACT-HAS-INFINITE-POWER`): what is infinite can
do every task that involves no contradiction (q.25 a.2). -/
def InfiniteActHasInfinitePower (σ : Signature) (Infinite : σ.Being → Prop) (P : Power σ) :
    Prop :=
  ∀ x, Infinite x → ∀ t, P.Consistent t → P.CanDo x t

/-- Intermediate (`NEW-GOD-IS-OMNIPOTENT`): whatever is God can do every task
that involves no contradiction (q.25 a.3). -/
def GodIsOmnipotent (σ : Signature) (P : Power σ) : Prop :=
  ∀ g, σ.IsGod g → ∀ t, P.Consistent t → P.CanDo g t

/-- OPEN (`NEW-REVELATION-INVOLVES-NO-CONTRADICTION`): revealing a truth with
signs involves no contradiction. -/
def RevelationInvolvesNoContradiction (σ : Signature) (P : Power σ) : Prop :=
  P.Consistent P.revealWithSigns

/-- OPEN (`NEW-SOME-SIGNS-ONLY-GOD-CAN-GIVE`): only God can reveal with the
signs in question (they exceed every created power), so whoever can give them
is God. -/
def SomeSignsOnlyGodCanGive (σ : Signature) (P : Power σ) : Prop :=
  ∀ x, P.CanDo x P.revealWithSigns → σ.IsGod x

/-- OPEN analyst bridge (`NEW-RECOGNIZABLE-REVELATION-ANALYSIS`): an analysis of
the skeleton's primitive `RevealsRecognizably`: a being reveals recognizably if
it can reveal with signs that only God can give. It gives a sufficient
condition only, not a definition of the field. -/
def RecognizableRevelationAnalysis (σ : Signature) (P : Power σ) : Prop :=
  ∀ g, P.CanDo g P.revealWithSigns → (∀ x, P.CanDo x P.revealWithSigns → σ.IsGod x) →
    σ.RevealsRecognizably g

/-! ## Controls: one joint witness and omission models

Formal-schema models only (two beings, `true` is the God). They show that the
batch is not vacuous and that each premise of the four target-reaching
derivations carries weight; they are not possible worlds of history. -/

namespace Control

/-- A two-being signature: `true` is God with the classical attributes,
`RevealsRecognizably` is `rr`, `FoundedAsTeachingAuthority` is `fta`, and a
society definitively proposes `p` exactly when `dp p`. -/
def sig (rr fta : Prop) (dp : Prop → Prop) : Signature where
  Being := Bool
  IsGod b := b = true
  HasClassicalAttributes _ := True
  RevealsRecognizably _ := rr
  jesus := false
  ClaimedDivineAuthority _ := True
  RoseFromTheDead _ := True
  Society := Unit
  catholicChurch := ()
  Founded _ _ := True
  VisibleWithAuthority _ := True
  FoundedAsTeachingAuthority _ _ := fta
  DefinitivelyProposesAsRevealed _ p := dp p
  creedOneGodFatherAlmightyCreator := True
  creedOneLordJesusChristOnlyBegottenConsubstantial := True
  creedIncarnateOfSpiritAndVirginMary := True
  creedCrucifiedUnderPilateSufferedBuried := True
  creedRoseOnTheThirdDay := True
  creedAscendedSeatedAtRightHand := True
  creedWillComeToJudgeKingdomWithoutEnd := True
  creedHolySpiritLordGiverOfLife := True
  creedOneHolyCatholicApostolicChurch := True
  creedOneBaptismForForgiveness := True
  creedResurrectionOfTheDead := True
  creedLifeOfTheWorldToCome := True

/-- An agency whose confirmation relation is `conf`. -/
def agency (rr fta : Prop) (dp : Prop → Prop) (conf : Prop → Prop) : Agency (sig rr fta dp) where
  Confirms _ p := conf p
  HoldsMandate _ _ := True
  FoundedInMandate _ _ _ := True
  CommissionedToTeach _ _ := True

/-- Veracity with asserting, believing and knowing given by `a`, `b`, `k`. -/
def veracity (rr fta : Prop) (dp : Prop → Prop) (a b k : Prop → Prop) :
    Veracity (sig rr fta dp) where
  Asserts _ p := a p
  Believes _ p := b p
  Knows _ p := k p

/-- Assistance that always holds. -/
def assistance (rr fta : Prop) (dp : Prop → Prop) : Assistance (sig rr fta dp) where
  Assists _ _ := True

/-- One task (revealing with signs) and one perfection; the task is consistent
iff `cons`, `x` can do it iff `can x`, it requires the perfection, the God is
in act in it, and it is possible. -/
def power (rr fta : Prop) (dp : Prop → Prop) (cons : Prop) (can : Bool → Prop) :
    Power (sig rr fta dp) where
  Task := Unit
  revealWithSigns := ()
  Consistent _ := cons
  CanDo x _ := can x
  Perfection := Unit
  Requires _ _ := True
  InAct x _ := x = true
  PossibleAct _ := True

/-- The joint-witness signature: revelation recognizable, the Church founded,
and definitive proposals exactly the truths. -/
abbrev jσ : Signature := sig True True (fun p => p)
abbrev jA : Agency jσ := agency True True (fun p => p) (fun p => p)
abbrev jV : Veracity jσ := veracity True True (fun p => p) (fun p => p) (fun p => p) (fun p => p)
abbrev jS : Assistance jσ := assistance True True (fun p => p)
abbrev jP : Power jσ := power True True (fun p => p) True (fun x => x = true)
abbrev jInfinite : jσ.Being → Prop := fun x => x = true

/-- Naming model: `true` is the only cause of being of the other and the only
maximum in being; it is God. -/
def nInAct (_ : Bool) (_ : Unit) : Prop := True
def nCauses (c _ : Bool) (_ : Unit) : Prop := c = true
def nMore (_ : Unit) (x y : Bool) : Prop := x = true ∧ y = false
def nGod (x : Bool) : Prop := x = true
def nComp (_ _ : Bool) : Prop := False

/-- Joint witness: every premise and conclusion of the batch holds in one model
with a God that has the classical attributes, founds the Church, causes the
being of the other being and can reveal with signs. -/
def JointWitness : Prop :=
  jσ.IsGod true ∧ jσ.HasClassicalAttributes true ∧ jσ.FoundedAsTeachingAuthority true () ∧
  ConfirmingIsAsserting jσ jA jV ∧ GodAssertsOnlyWhatHeKnows jσ jV ∧
  GodKnowsOnlyTruths jσ jV ∧ ClassicalAttributesIncludePerfectIntellectAndGoodWill jσ jV ∧
  GodConfirmsOnlyTruth jσ jA ∧
  FounderGuaranteesFoundedAuthority jσ jS ∧ AssistedDefinitiveProposalIsConfirmed jσ jA jS ∧
  DefinitiveProposalIsGodConfirmed jσ jA ∧ BridgeGodFoundedAuthorityProposesOnlyTruth jσ ∧
  InfiniteIsUnlimitedAct jσ jInfinite jP ∧ ActivePowerFollowsAct jσ jP ∧
  ConsistentTaskRequiresOnlyPossiblePerfections jσ jP ∧ InfiniteActHasInfinitePower jσ jInfinite jP ∧
  GodIsInfinite jσ.IsGod jInfinite ∧ GodIsOmnipotent jσ jP ∧
  RevelationInvolvesNoContradiction jσ jP ∧ SomeSignsOnlyGodCanGive jσ jP ∧
  RecognizableRevelationAnalysis jσ jP ∧ RevelationPossibleAndRecognizable jσ ∧
  CausesAllInGenus nInAct nCauses () true ∧
  NameGodImposedFromOperation nInAct nCauses () nGod ∧
  UniversalCauseOfBeingIsMaximal nInAct nMore nCauses () ∧
  GodNamesTheUniqueMaximeEns nInAct nMore nCauses () nGod ∧
  GodNamesTheFullyDescribedPrinciple nInAct nMore nCauses () nComp nGod

/-- Omission models for the veracity derivation: each of its three premises
fails in a model of the other two where some confirmed proposition is false. -/
def VeracityOmissions : Prop :=
  (∃ σ : Signature, ∃ A : Agency σ, ∃ V : Veracity σ, ¬ ConfirmingIsAsserting σ A V ∧
    GodAssertsOnlyWhatHeKnows σ V ∧ GodKnowsOnlyTruths σ V ∧ ¬ GodConfirmsOnlyTruth σ A) ∧
  (∃ σ : Signature, ∃ A : Agency σ, ∃ V : Veracity σ, ConfirmingIsAsserting σ A V ∧
    ¬ GodAssertsOnlyWhatHeKnows σ V ∧ GodKnowsOnlyTruths σ V ∧ ¬ GodConfirmsOnlyTruth σ A) ∧
  (∃ σ : Signature, ∃ A : Agency σ, ∃ V : Veracity σ, ConfirmingIsAsserting σ A V ∧
    GodAssertsOnlyWhatHeKnows σ V ∧ ¬ GodKnowsOnlyTruths σ V ∧ ¬ GodConfirmsOnlyTruth σ A)

/-- Omission models for the authority step: without either premise the bridge
fails. -/
def AuthorityOmissions : Prop :=
  (∃ σ : Signature, ∃ A : Agency σ, ¬ DefinitiveProposalIsGodConfirmed σ A ∧
    GodConfirmsOnlyTruth σ A ∧ ¬ BridgeGodFoundedAuthorityProposesOnlyTruth σ) ∧
  (∃ σ : Signature, ∃ A : Agency σ, DefinitiveProposalIsGodConfirmed σ A ∧
    ¬ GodConfirmsOnlyTruth σ A ∧ ¬ BridgeGodFoundedAuthorityProposesOnlyTruth σ)

/-- Omission models for the revelation step: each of its four premises fails in
a model of the other three where some God does not reveal recognizably. -/
def RevelationOmissions : Prop :=
  (∃ σ : Signature, ∃ P : Power σ, ¬ GodIsOmnipotent σ P ∧
    RevelationInvolvesNoContradiction σ P ∧ SomeSignsOnlyGodCanGive σ P ∧
    RecognizableRevelationAnalysis σ P ∧ ¬ RevelationPossibleAndRecognizable σ) ∧
  (∃ σ : Signature, ∃ P : Power σ, GodIsOmnipotent σ P ∧
    ¬ RevelationInvolvesNoContradiction σ P ∧ SomeSignsOnlyGodCanGive σ P ∧
    RecognizableRevelationAnalysis σ P ∧ ¬ RevelationPossibleAndRecognizable σ) ∧
  (∃ σ : Signature, ∃ P : Power σ, GodIsOmnipotent σ P ∧
    RevelationInvolvesNoContradiction σ P ∧ ¬ SomeSignsOnlyGodCanGive σ P ∧
    RecognizableRevelationAnalysis σ P ∧ ¬ RevelationPossibleAndRecognizable σ) ∧
  (∃ σ : Signature, ∃ P : Power σ, GodIsOmnipotent σ P ∧
    RevelationInvolvesNoContradiction σ P ∧ SomeSignsOnlyGodCanGive σ P ∧
    ¬ RecognizableRevelationAnalysis σ P ∧ ¬ RevelationPossibleAndRecognizable σ)

/-- Omission models for the operation-naming step (two beings, one respect). -/
def NamingOmissions : Prop :=
  (∃ (InAct : Bool → Unit → Prop) (MoreIn : Unit → Bool → Bool → Prop)
      (CausesIn : Bool → Bool → Unit → Prop) (God : Bool → Prop),
    ¬ NameGodImposedFromOperation InAct CausesIn () God ∧
    UniversalCauseOfBeingIsMaximal InAct MoreIn CausesIn () ∧
    ¬ GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn () God) ∧
  (∃ (InAct : Bool → Unit → Prop) (MoreIn : Unit → Bool → Bool → Prop)
      (CausesIn : Bool → Bool → Unit → Prop) (God : Bool → Prop),
    NameGodImposedFromOperation InAct CausesIn () God ∧
    ¬ UniversalCauseOfBeingIsMaximal InAct MoreIn CausesIn () ∧
    ¬ GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn () God)

/-- The batch controls. -/
def Certificate : Prop :=
  JointWitness ∧ VeracityOmissions ∧ AuthorityOmissions ∧ RevelationOmissions ∧ NamingOmissions

end Control

end TruthCore.Causality.NamingVeracityBatch1
