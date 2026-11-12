module

public import TruthCore.Causality.DeiFiliusUnifiedRoute
public import TruthCore.Results.Causality.DeiFiliusAttributeField.Solution
public import TruthCore.Results.Causality.NecessaryClassicalGodRootControl.Solution

/-! The unified Dei Filius route: the restated sufficiency and the Dei Filius root
with every primitive through its typed sense and sense bridge at once, the
derivation of `CausedIsNotInfinite` from the reception-limitation premises, and
two joint-satisfiability models. Analyst formulations, attribution deferred. No
premise is established. -/

@[expose] public section

namespace TruthCore.Results.Causality.DeiFiliusUnifiedRoute

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Causality.DeiFiliusAttributeField
open TruthCore.Causality.DeiFiliusLivingNineScope (HasTheNine NineLiveSomeTime)
open TruthCore.Causality.DeiFiliusLivingSelfOperation (PureActLifeAtSomeTimeIsLiving)
open TruthCore.Causality.DeiFiliusLordBlessed
open TruthCore.Causality.DeiFiliusImmenseIncomprehensible
open TruthCore.Causality.Round2PerfectionPrimacy
  (CausedInBeingByAnotherIsCreature CreatureEsseIsReceived)
open TruthCore.Causality.ReceptionLimitation (ReceivedEsseIsLimited InfiniteEsseIsUnlimited)
open TruthCore.Causality.NamingVeracityBatch1 (Power InfiniteActHasInfinitePower)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic

/-- What has its being caused by another is not INFINITE_1, from four existing
open premises: x, caused in being by some c ≠ x, is a creature; a creature's esse
is received in some principle; received esse is limited; an INFINITE_1 being's
esse is not limited. The step from caused to received being runs through
`Creature`. -/
theorem causedIsNotInfiniteFromReception {B R P : Type}
    (CausesIn : B → B → R → Prop) (esse : R) (Infinite Creature EsseLimited : B → Prop)
    (EsseReceivedIn : B → P → Prop)
    (hCreature : CausedInBeingByAnotherIsCreature CausesIn Creature esse)
    (hReceived : CreatureEsseIsReceived Creature EsseReceivedIn)
    (hLimited : ReceivedEsseIsLimited EsseLimited EsseReceivedIn)
    (hUnlimited : InfiniteEsseIsUnlimited EsseLimited Infinite) :
    CausedIsNotInfinite CausesIn esse Infinite := by
  intro x ⟨c, hne, hc⟩ hInf
  obtain ⟨z, hz⟩ := hReceived x (hCreature c x hne hc)
  exact hUnlimited x hInf (hLimited x z hz)

/-- Within the unified root bundle: the root's infinity premise (esse equal to
essence suffices for INFINITE_1) and `CausedIsNotInfinite` together give that
whatever has its being caused by another being distinct from it has (represented)
esse distinct from its essence. A checked lemma, deliberately not registered as a
corpus argument. -/
theorem causedHasDistinctEsse {B P R : Type} (CausesIn : B → B → R → Prop) (esse : R)
    (essenceOf esseOf : B → P) (Infinite : B → Prop)
    (hInfinity : SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite)
    (hCaused : CausedIsNotInfinite CausesIn esse Infinite) :
    ∀ c x, c ≠ x → CausesIn c x esse → esseOf x ≠ essenceOf x :=
  fun c x hne hc hEq => hCaused x ⟨c, hne, hc⟩ (hInfinity x hEq)

/-- The primitives that agree with `D` except that each of the five is replaced
by the antecedent of its old bridge, so that the five old bridges hold
trivially and nothing about the given primitives is used. -/
private abbrev trivialPrims {Being Respect : Type} (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (Infinite HasIntellect : Being → Prop) : Primitives Being :=
  { Lives := HasIntellect
    IsLord := IsCreatorOfAll InAct CausesIn esse
    Immense := IsCreatorOfAll InAct CausesIn esse
    Incomprehensible := Infinite
    MostBlessed := fun x => IsPerfect InAct x ∧ HasIntellect x }

/-- The restated sufficiency (`NineSufficeForDeiFilius`) with all five primitives
through their typed senses at once. The registered `nineGiveDeiFilius` is applied
with none of the five old bridges, on the primitives whose living, lord, immense,
incomprehensible and most-blessed fields are the antecedents of those bridges;
the bridges then hold trivially and nothing about `D` is used. At the being `g`
with the nine: LIVING_2 from the nine and the restricted sense bridge (g is pure
act) give `D.Lives g`; LORD_2, BLESSED_2, IMMENSE_2 and INCOMPREHENSIBLE_2 from the
nine and their sense bridges give the other four. Every other conjunct is carried
over. -/
theorem nineGiveDeiFiliusUnified (σ : Signature) {Principle Respect Time : Type}
    (InAct GoodIn InPotency : σ.Being → Respect → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (MoreIn : Respect → σ.Being → σ.Being → Prop) (ComponentOf : σ.Being → σ.Being → Prop)
    (essenceOf esseOf : σ.Being → Principle)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (P : Power σ) (D : Primitives σ.Being) (LivesAt : σ.Being → Time → Prop)
    (Governs : σ.Being → σ.Being → Prop) (understanding : Respect) (C : Comprehension σ.Being)
    (hNineLive : NineLiveSomeTime InAct GoodIn InPotency CausesIn esse σ.IsGod Composite
      Infinite Eternal HasIntellect HasWill LivesAt)
    (hLivingSense : PureActLifeAtSomeTimeIsLiving InPotency LivesAt D)
    (hNineLord : NineAreLordByCauseAndGovernment InAct GoodIn InPotency CausesIn esse σ.IsGod
      Composite Infinite Eternal HasIntellect HasWill Governs)
    (hLordSense : CauseAndGovernorOfAllIsLord InAct CausesIn esse Governs D)
    (hNineBlessed : NineAreBlessedByUnderstanding InAct GoodIn InPotency CausesIn esse
      understanding σ.IsGod Composite Infinite Eternal HasIntellect HasWill)
    (hBlessedSense : UnderstandingPerfectIsMostBlessed InAct GoodIn esse understanding
      HasIntellect D)
    (hNineImmense : NineAreImmenseAsInfiniteCauseOfAll InAct GoodIn InPotency CausesIn esse
      σ.IsGod Composite Infinite Eternal HasIntellect HasWill)
    (hImmenseSense : InfiniteCauseOfAllIsImmense InAct CausesIn esse Infinite D)
    (hNineIncomprehensible : NineAreIncomprehensibleToCausedIntellects InAct GoodIn InPotency
      CausesIn esse σ.IsGod Composite Infinite Eternal HasIntellect HasWill C)
    (hIncomprehensibleSense : InfiniteUncomprehendedIsIncomprehensible CausesIn esse Infinite
      HasIntellect C D)
    (hPower : InfiniteActHasInfinitePower σ Infinite P)
    (hNoComponent : CreatorOfAllIsNoComponent InAct CausesIn esse ComponentOf)
    (hExcess : ExcessInBeingIsExcessInAct InAct MoreIn esse)
    (hGoodness : GoodnessIsActualityReading GoodIn InAct)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite essenceOf esseOf) :
    NineSufficeForDeiFilius σ InAct GoodIn InPotency CausesIn esse MoreIn ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill P D := by
  intro g hNine
  have h := TruthCore.Results.Causality.DeiFiliusAttributeField.nineGiveDeiFilius σ InAct GoodIn
    InPotency CausesIn esse MoreIn ComponentOf essenceOf esseOf Composite MatterForm Infinite
    Eternal HasIntellect HasWill P (trivialPrims InAct CausesIn esse Infinite HasIntellect)
    (fun _ hx => hx) (fun _ hx => hx) hPower (fun _ hx => hx) (fun _ hx => hx)
    (fun _ hp hx => ⟨hp, hx⟩) hNoComponent hExcess hGoodness hKinds g hNine
  exact
    { one := h.one
      living := hLivingSense g h.immutable (hNineLive g hNine)
      creator := h.creator
      lord := hLordSense g (hNineLord g hNine)
      almighty := h.almighty
      eternal := h.eternal
      immense := hImmenseSense g (hNineImmense g hNine)
      incomprehensible := hIncomprehensibleSense g (hNineIncomprehensible g hNine)
      intellect := h.intellect
      will := h.will
      perfect := h.perfect
      infinite := h.infinite
      simple := h.simple
      immutable := h.immutable
      spiritual := h.spiritual
      distinct := h.distinct
      blessed := hBlessedSense g (hNineBlessed g hNine)
      exalted := h.exalted
      good := h.good }

/-- The spine's root has every typed Dei Filius attribute, with all five
primitives through their typed senses at once. The registered `deiFiliusRoot` is
applied with none of the five old bridges, on the same modified primitives as
above. Its root `n` has the nine (`nineOfDeiFilius`, a projection; none of the
nine is a primitive), so the five nine-statements and the five sense bridges give
`n` the five primitives of `D`. -/
theorem deiFiliusRootUnified {W Principle Respect Time : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being Principle Respect)
    (GoodIn InPotency : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (Pw : Power σ) (D : Primitives σ.Being) (LivesAt : σ.Being → Time → Prop)
    (Governs : σ.Being → σ.Being → Prop) (understanding : Respect) (C : Comprehension σ.Being)
    (hUnderived : NecessaryConcreteUnderivedAt m w) (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading p.InAct MoreIn p.CausesIn p.esse)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hApproach : GradesToMaximumAtBeing p.InAct MoreIn p.esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading p.InAct p.esse)
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading p.InAct p.CausesIn p.esse)
    (hGoodness : GoodnessIsActualityReading GoodIn p.InAct)
    (hTransfer : UniversalCauseTransfersPerfections p.InAct p.CausesIn p.esse)
    (hUniting : CompositeHasAUnitingCauseReading Composite p.CausesIn p.esse)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite p.essenceOf p.esseOf)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hIntellect : ImmaterialIsIntellectualReading MatterForm HasIntellect ComponentOf)
    (hWill : WillFollowsIntellectReading HasIntellect HasWill)
    (hActPrior : TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic.IndependentPriority
      p.InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading p.InAct InPotency)
    (hInfinity : SubsistentBeingIsInfiniteReading p.essenceOf p.esseOf Infinite)
    (hEternity : ImmutableIsEternalReading InPotency Eternal)
    (hNaming : GodNamesTheFullyDescribedPrinciple p.InAct MoreIn p.CausesIn p.esse ComponentOf σ.IsGod)
    (hGodMaximal : GodIsMaximalInBeing σ.IsGod p.InAct MoreIn p.esse)
    (hNineLive : NineLiveSomeTime p.InAct GoodIn InPotency p.CausesIn p.esse σ.IsGod Composite
      Infinite Eternal HasIntellect HasWill LivesAt)
    (hLivingSense : PureActLifeAtSomeTimeIsLiving InPotency LivesAt D)
    (hNineLord : NineAreLordByCauseAndGovernment p.InAct GoodIn InPotency p.CausesIn p.esse
      σ.IsGod Composite Infinite Eternal HasIntellect HasWill Governs)
    (hLordSense : CauseAndGovernorOfAllIsLord p.InAct p.CausesIn p.esse Governs D)
    (hNineBlessed : NineAreBlessedByUnderstanding p.InAct GoodIn InPotency p.CausesIn p.esse
      understanding σ.IsGod Composite Infinite Eternal HasIntellect HasWill)
    (hBlessedSense : UnderstandingPerfectIsMostBlessed p.InAct GoodIn p.esse understanding
      HasIntellect D)
    (hNineImmense : NineAreImmenseAsInfiniteCauseOfAll p.InAct GoodIn InPotency p.CausesIn p.esse
      σ.IsGod Composite Infinite Eternal HasIntellect HasWill)
    (hImmenseSense : InfiniteCauseOfAllIsImmense p.InAct p.CausesIn p.esse Infinite D)
    (hNineIncomprehensible : NineAreIncomprehensibleToCausedIntellects p.InAct GoodIn InPotency
      p.CausesIn p.esse σ.IsGod Composite Infinite Eternal HasIntellect HasWill C)
    (hIncomprehensibleSense : InfiniteUncomprehendedIsIncomprehensible p.CausesIn p.esse Infinite
      HasIntellect C D)
    (hPower : InfiniteActHasInfinitePower σ Infinite Pw) :
    NecessaryDeiFiliusGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill Pw D := by
  obtain ⟨n, hPerfectRoot, hId, hFirst, hNoMF, hRemote, hGod, h⟩ :=
    TruthCore.Results.Causality.DeiFiliusAttributeField.deiFiliusRoot σ m w p GoodIn InPotency
      MoreIn PriorSimply ComponentOf Composite MatterForm Infinite Eternal HasIntellect HasWill
      Pw (trivialPrims p.InAct p.CausesIn p.esse Infinite HasIntellect) hUnderived hEM hGenus
      hExisting hEsse hApproach hBeing hPreexist hGoodness hTransfer hUniting hKinds hPrior
      hNoComponent hIntellect hWill hActPrior hNotBoth hInfinity hEternity hNaming hGodMaximal
      (fun _ hx => hx) (fun _ hx => hx) hPower (fun _ hx => hx) (fun _ hx => hx)
      (fun _ hp hx => ⟨hp, hx⟩)
  have hNine := nineOfDeiFilius σ h
  exact ⟨n, hPerfectRoot, hId, hFirst, hNoMF, hRemote, hGod,
    { one := h.one
      living := hLivingSense n h.immutable (hNineLive n hNine)
      creator := h.creator
      lord := hLordSense n (hNineLord n hNine)
      almighty := h.almighty
      eternal := h.eternal
      immense := hImmenseSense n (hNineImmense n hNine)
      incomprehensible := hIncomprehensibleSense n (hNineIncomprehensible n hNine)
      intellect := h.intellect
      will := h.will
      perfect := h.perfect
      infinite := h.infinite
      simple := h.simple
      immutable := h.immutable
      spiritual := h.spiritual
      distinct := h.distinct
      blessed := hBlessedSense n (hNineBlessed n hNine)
      exalted := h.exalted
      good := h.good }⟩

section Controls

open TruthCore.Causality.DeiFiliusUnifiedRoute.Control
open TruthCore.Causality.RootPositiveIntellectWillControl (model)
open TruthCore.Causality.NecessaryClassicalGodRootControl (signature)

/-- On the two-being model, whatever has the nine is `true` (uniqueness). -/
private theorem nineIsTrue (g : Bool)
    (h : HasTheNine inAct inAct potency causes false isTrue composite isTrue isTrue yes yes g) :
    g = true :=
  (h.2.2.2.1 true rfl).symm

/-- On the two-being model, a cause of the being of all others is `true`. -/
private theorem creatorIsTrue (g : Bool) (h : IsCreatorOfAll inAct causes false g) : g = true := by
  cases g with
  | true => rfl
  | false => exact (h true (by decide) (Or.inl rfl)).1

private theorem trueHasNine :
    HasTheNine inAct inAct potency causes false isTrue composite isTrue isTrue yes yes true := by
  refine ⟨Bool.noConfusion, fun _ _ _ => Or.inl rfl, ⟨Or.inr rfl, ?_⟩, fun _ h => h,
    rfl, fun _ h => Bool.noConfusion h.1, rfl, trivial, trivial⟩
  intro x _ hx _
  cases x with
  | true => exact absurd rfl hx
  | false => exact ⟨rfl, rfl⟩

private theorem sufficiencyBundle : SufficiencyBundle := by
  refine ⟨fun _ _ => ⟨(), trivial⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun _ h => (creatorIsTrue _ h ▸ fun _ h => nomatch h), ?_, fun _ _ => Iff.rfl, ?_,
    fun _ _ => rfl, ?_, ?_, fun _ _ _ => ⟨(), trivial⟩, fun _ _ h => h, ?_,
    fun _ _ _ h => h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hPure _
    cases g with
    | true => rfl
    | false => exact absurd ⟨rfl, rfl⟩ (hPure true)
  · intro g hg
    have := nineIsTrue g hg
    subst this
    exact ⟨fun x hx hAct => trueHasNine.2.2.1.2 x false hx hAct, fun _ _ _ => rfl⟩
  · intro g hg
    exact creatorIsTrue g hg.1
  · intro g hg
    have := nineIsTrue g hg
    subst this
    exact ⟨trivial, fun _ _ _ => Or.inl rfl, Or.inr rfl, Or.inl rfl⟩
  · intro g hg
    cases g with
    | true => rfl
    | false =>
      cases hg.2.2.2 with
      | inl h => exact h
      | inr h => exact absurd h (by decide)
  · intro g hg
    have := nineIsTrue g hg
    subst this
    exact ⟨rfl, fun x hx hAct => trueHasNine.2.2.1.2 x false hx hAct⟩
  · intro g hg
    exact hg.1
  · intro g hg
    have := nineIsTrue g hg
    subst this
    refine ⟨rfl, fun x ⟨_, c, hne, hc⟩ hcomp => ?_⟩
    have hx : x = false := hc.2
    subst hx
    exact Bool.noConfusion hcomp
  · intro g hg
    exact hg.1
  · intro x hx _ _
    exact hx
  · intro y x ⟨hy, hx⟩
    subst hy
    subst hx
    exact ⟨true, Or.inl rfl, fun h => by cases h with
      | inl h => exact Bool.noConfusion h
      | inr h => exact Bool.noConfusion h⟩
  · intro x
    refine ⟨fun h => h.elim, fun hne => ?_⟩
    cases x with
    | true => exact absurd rfl hne
    | false => rfl
  · intro x _
    cases x with
    | true => exact Or.inl (Or.inl rfl)
    | false => exact Or.inr ⟨rfl, rfl⟩
  · intro x _ hAct
    cases hAct with
    | inl h => exact h
    | inr h => exact absurd h (by decide)
  · intro g _ _ hc x hx _
    exact ⟨(), creatorIsTrue g hc⟩
  · intro x ⟨c, hne, hc⟩ hInf
    rw [hc.2] at hInf
    exact Bool.noConfusion hInf
  · intro _ _ _ hc
    exact hc.2
  · intro x hx
    exact ⟨true, hx, rfl⟩
  · intro x _ h
    exact h.1
  · intro x hInf hLim
    rw [hLim] at hInf
    exact Bool.noConfusion hInf
  · intro g x hg _ hx hcomp
    exact hx (hcomp ▸ hg)

private theorem rootIsSource (g : TransferRole)
    (h : IsCreatorOfAll rootProfile.InAct rootProfile.CausesIn rootProfile.esse g) :
    g = .source := by
  cases g with
  | source => rfl
  | supporter =>
    have := h .source (by decide) trivial
    change transferCause true .supporter .source false at this
    unfold transferCause at this
    exact absurd this (by decide)
  | producer =>
    have := h .source (by decide) trivial
    change transferCause true .producer .source false at this
    unfold transferCause at this
    exact absurd this (by decide)
  | recipient =>
    have := h .source (by decide) trivial
    change transferCause true .recipient .source false at this
    unfold transferCause at this
    exact absurd this (by decide)

/-- Nothing causes the being of `source`. -/
private theorem rootNoIncoming (c : TransferRole) :
    ¬ rootProfile.CausesIn c .source rootProfile.esse := by
  intro h
  change transferCause true c .source false at h
  unfold transferCause at h
  cases c <;> exact absurd h (by decide)

private theorem rootSourceCausesOthers (x : TransferRole) (hx : x ≠ .source) :
    rootProfile.CausesIn .source x rootProfile.esse := by
  change transferCause true .source x false
  unfold transferCause
  cases x
  · exact absurd rfl hx
  all_goals decide

private theorem rootNineIsSource (g : TransferRole)
    (h : HasTheNine rootProfile.InAct transferAct rootPotency rootProfile.CausesIn
      rootProfile.esse signature.IsGod rootComposite rootInfinite
      TruthCore.Causality.NecessaryClassicalGodRootControl.eternal
      TruthCore.Causality.RootPositiveIntellectWillControl.intellect
      TruthCore.Causality.RootPositiveIntellectWillControl.will g) : g = .source :=
  h.2.2.2.2.1

private theorem rootCreatorSource :
    IsCreatorOfAll rootProfile.InAct rootProfile.CausesIn rootProfile.esse .source :=
  fun x hx _ => rootSourceCausesOthers x hx

private theorem rootBundle (hEM : ExcludedMiddle) : RootBundle := by
  have hOld := TruthCore.Results.Causality.RootPositiveIntellectWillControl.checks hEM
  rcases hOld.2.1 with ⟨hPop, hWhole, hDep, hGenus, hExisting, hEsse, hApproach, hBeing,
    hPreexist, hGoodness, hTransfer, _, _, hPrior, hNoComponent, hIntellect, hWill⟩
  have hNew := TruthCore.Results.Causality.NecessaryClassicalGodRootControl.checks hEM
  rcases hNew.2.1 with ⟨_, hActPrior, hNotBoth, _, hEternity, hNaming, hMaximal, _⟩
  have hNecessary := hNew.2.2.2.2.2.2.2.1
  refine ⟨⟨.source, trivial, trivial, hNecessary .source, fun _ a _ _ h => rootNoIncoming a h⟩,
    hGenus, hExisting, hEsse, hApproach, hBeing, hPreexist, hGoodness, hTransfer, ?_, ?_,
    hPrior, hNoComponent, hIntellect, hWill, hActPrior, hNotBoth, ?_, hEternity, hNaming,
    hMaximal, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  -- uniting cause
  · intro x hx
    exact ⟨.source, fun h => hx h.symm, rootSourceCausesOthers x hx⟩
  -- kinds
  · intro x
    refine ⟨fun h => ?_, fun hne h => hne ?_⟩
    · change x = TransferRole.producer at h
      subst h
      exact TransferRole.noConfusion
    · change x = TransferRole.source
      exact h
  -- infinity
  · intro x h
    exact h
  -- NineLiveSomeTime
  · intro g hg
    rw [rootNineIsSource g hg]
    exact ⟨(), Or.inl rfl⟩
  -- living sense bridge
  · intro g _ ⟨_, h⟩
    exact h
  -- NineAreLord
  · intro g hg
    rw [rootNineIsSource g hg]
    exact ⟨rootCreatorSource, fun _ _ _ => rfl⟩
  -- lord sense bridge
  · intro g hg
    exact rootIsSource g hg.1
  -- NineAreBlessed
  · intro g hg
    rw [rootNineIsSource g hg]
    exact ⟨Or.inl rfl, fun _ _ _ => trivial, trivial, trivial⟩
  -- blessed sense bridge
  · intro g hg
    exact hg.1
  -- NineAreImmense
  · intro g hg
    rw [rootNineIsSource g hg]
    exact ⟨rfl, rootCreatorSource⟩
  -- immense sense bridge
  · intro g hg
    exact hg.1
  -- NineAreIncomprehensible
  · intro g hg
    rw [rootNineIsSource g hg]
    refine ⟨rfl, fun x ⟨_, c, _, hc⟩ hcomp => ?_⟩
    change x = TransferRole.source at hcomp
    subst hcomp
    exact rootNoIncoming c hc
  -- incomprehensible sense bridge
  · intro g hg
    exact hg.1
  -- power
  · intro x hx _ _
    exact hx
  -- capacity to understand
  · intro x hx
    exact hx
  -- exercised or in potency
  · intro _ _
    exact Or.inl trivial
  -- exercised understanding is immanent operation
  · intro x hx _
    exact hx
  -- self-operating unmoved lives
  · intro x hx _
    exact ⟨(), hx⟩
  -- moved only as in potency
  · intro _ _ h
    exact h
  -- directing bridge
  · intro g _ _ hc _ _ _
    exact ⟨(), rootIsSource g hc⟩
  -- directing is governing
  · intro _ _ _ h
    exact h
  -- caused is not infinite
  · intro x ⟨c, _, hc⟩ hInf
    change x = TransferRole.source at hInf
    subst hInf
    exact rootNoIncoming c hc
  -- caused in being by another is a creature
  · intro c x _ hc hx
    change x = TransferRole.source at hx
    subst hx
    exact rootNoIncoming c hc
  -- creature esse is received
  · intro x hx
    exact ⟨.source, hx, rfl⟩
  -- received esse is limited
  · intro x _ h
    exact h.1
  -- infinite esse is unlimited
  · intro x hInf hLim
    exact hLim hInf
  -- finite intellect does not comprehend the infinite
  · intro g x hg _ hx hcomp
    change x = g at hcomp
    subst hcomp
    exact hx hg

/-- The controls of `Control.Controls`, checked on the two explicit
interpretations. -/
theorem controls : TruthCore.Causality.DeiFiliusUnifiedRoute.Control.Controls := by
  refine ⟨⟨sufficiencyBundle, trueHasNine, ?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨hL, hLS, hLo, hLoS, hB, hBS, hI, hIS, hN, hNS, hP, hNC, hE, hG, hK, _⟩ :=
      sufficiencyBundle
    exact nineGiveDeiFiliusUnified sig inAct inAct potency causes false more noComponent essence
      esseOf composite noMatterForm isTrue isTrue yes yes power prims livesAt governs true
      selfComprehension hL hLS hLo hLoS hB hBS hI hIS hN hNS hP hNC hE hG hK true trueHasNine
  · intro h
    exact Bool.noConfusion (h false trivial)
  · intro hEM
    obtain ⟨hU, hGenus, hExisting, hEsse, hApproach, hBeing, hPreexist, hGoodness, hTransfer,
      hUniting, hKinds, hPrior, hNoComponent, hIntellect, hWill, hActPrior, hNotBoth, hInfinity,
      hEternity, hNaming, hMaximal, hL, hLS, hLo, hLoS, hBl, hBlS, hI, hIS, hN, hNS, hP, _⟩ := rootBundle hEM
    exact ⟨rootBundle hEM, deiFiliusRootUnified signature model false rootProfile transferAct rootPotency
      (transferMore true) TruthCore.Causality.RootPositiveIntellectWillControl.prior
      TruthCore.Causality.RootPositiveIntellectWillControl.component rootComposite
      TruthCore.Causality.RootPositiveIntellectWillControl.matterForm rootInfinite
      TruthCore.Causality.NecessaryClassicalGodRootControl.eternal
      TruthCore.Causality.RootPositiveIntellectWillControl.intellect
      TruthCore.Causality.RootPositiveIntellectWillControl.will rootPower rootPrims rootLivesAt
      rootGoverns true rootComprehension hU hEM hGenus hExisting hEsse hApproach hBeing hPreexist
      hGoodness hTransfer hUniting hKinds hPrior hNoComponent hIntellect hWill hActPrior hNotBoth
      hInfinity hEternity hNaming hMaximal hL hLS hLo hLoS hBl hBlS hI hIS hN hNS hP⟩
  · intro h
    apply h .supporter ⟨.source, by decide, by
      change transferCause true .source .supporter false
      unfold transferCause
      decide⟩
    rfl

end Controls

end TruthCore.Results.Causality.DeiFiliusUnifiedRoute
