module

public import TruthCore.Causality.DeiFiliusLivingSelfOperation
public import TruthCore.Results.Causality.DeiFiliusAttributeField.Solution

/-! *Vivus* at the spine's root from the time-indexed self-operation route and
one restricted sense bridge, in place of the intellect-gives-life bridge.
Analyst formulations, attribution deferred. No premise is established. -/

@[expose] public section

namespace TruthCore.Results.Causality.DeiFiliusLivingSelfOperation

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Causality.DeiFiliusAttributeField
open TruthCore.Causality.DeiFiliusLivingSelfOperation
open TruthCore.Causality.NamingVeracityBatch1 (Power InfiniteActHasInfinitePower)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic

/-- The restated sufficiency (`NineSufficeForDeiFilius`) with its LIVING_1
conjunct derived from pure act rather than from intellect. Among the nine is
altogether immutability, whose body is `PureAct InPotency g`. The registered
`nineGiveDeiFilius` is applied, without `IntellectualIsLiving`, to the
primitives that agree with `D` except that their `Lives` is `HasIntellect`;
`STMT-PURE-ACT-LIVES` gives `g` life at some time of the frame (LIVING_2), and
the restricted sense bridge gives `D.Lives g` (LIVING_1). Every other conjunct
is carried over unchanged. -/
theorem nineGiveDeiFiliusLivingFromPureAct (σ : Signature) {Principle Respect Time : Type}
    (InAct GoodIn InPotency : σ.Being → Respect → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (MoreIn : Respect → σ.Being → σ.Being → Prop) (ComponentOf : σ.Being → σ.Being → Prop)
    (essenceOf esseOf : σ.Being → Principle)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (P : Power σ) (D : Primitives σ.Being) (LivesAt : σ.Being → Time → Prop)
    (hPureLives : PureActLivesReading InPotency LivesAt)
    (hSense : PureActLifeAtSomeTimeIsLiving InPotency LivesAt D)
    (hLord : CreatorOfAllIsLord InAct CausesIn esse D)
    (hPower : InfiniteActHasInfinitePower σ Infinite P)
    (hImmense : CreatorOfAllIsImmense InAct CausesIn esse D)
    (hIncomprehensible : InfiniteIsIncomprehensible Infinite D)
    (hBlessed : PerfectIntellectualIsMostBlessed InAct HasIntellect D)
    (hNoComponent : CreatorOfAllIsNoComponent InAct CausesIn esse ComponentOf)
    (hExcess : ExcessInBeingIsExcessInAct InAct MoreIn esse)
    (hGoodness : GoodnessIsActualityReading GoodIn InAct)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite essenceOf esseOf) :
    NineSufficeForDeiFilius σ InAct GoodIn InPotency CausesIn esse MoreIn ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill P D := by
  intro g hNine
  let D' : Primitives σ.Being := { D with Lives := HasIntellect }
  have h := TruthCore.Results.Causality.DeiFiliusAttributeField.nineGiveDeiFilius σ InAct GoodIn
    InPotency CausesIn esse MoreIn ComponentOf essenceOf esseOf Composite MatterForm Infinite
    Eternal HasIntellect HasWill P D' (fun _ hx => hx) hLord hPower hImmense hIncomprehensible
    hBlessed hNoComponent hExcess hGoodness hKinds g hNine
  exact
    { one := h.one
      living := hSense g h.immutable (hPureLives g h.immutable)
      creator := h.creator
      lord := h.lord
      almighty := h.almighty
      eternal := h.eternal
      immense := h.immense
      incomprehensible := h.incomprehensible
      intellect := h.intellect
      will := h.will
      perfect := h.perfect
      infinite := h.infinite
      simple := h.simple
      immutable := h.immutable
      spiritual := h.spiritual
      distinct := h.distinct
      blessed := h.blessed
      exalted := h.exalted
      good := h.good }

/-- The spine's root has every typed Dei Filius attribute, with its LIVING_1
conjunct derived from the root's pure act rather than from its intellect. The
registered `deiFiliusRoot` is applied, without `IntellectualIsLiving`, to the
primitives that agree with `D` except that their `Lives` is `HasIntellect` (so
the bridge holds trivially there and nothing about `D.Lives` is used). Its root
`n` is the same witness, and its `immutable` conjunct is `PureAct InPotency n`.
The time-indexed `STMT-PURE-ACT-LIVES` gives `n` life at some time of the frame
(LIVING_2), and the restricted sense bridge gives `D.Lives n` (LIVING_1). Every
other conjunct is carried over unchanged. -/
theorem deiFiliusRootLivingFromPureAct {W Principle Respect Time : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being Principle Respect)
    (GoodIn InPotency : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (Pw : Power σ) (D : Primitives σ.Being) (LivesAt : σ.Being → Time → Prop)
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
    (hPureLives : PureActLivesReading InPotency LivesAt)
    (hSense : PureActLifeAtSomeTimeIsLiving InPotency LivesAt D)
    (hLord : CreatorOfAllIsLord p.InAct p.CausesIn p.esse D)
    (hPower : InfiniteActHasInfinitePower σ Infinite Pw)
    (hImmense : CreatorOfAllIsImmense p.InAct p.CausesIn p.esse D)
    (hIncomprehensible : InfiniteIsIncomprehensible Infinite D)
    (hBlessed : PerfectIntellectualIsMostBlessed p.InAct HasIntellect D) :
    NecessaryDeiFiliusGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill Pw D := by
  let D' : Primitives σ.Being := { D with Lives := HasIntellect }
  obtain ⟨n, hPerfectRoot, hId, hFirst, hNoMF, hRemote, hGod, h⟩ :=
    TruthCore.Results.Causality.DeiFiliusAttributeField.deiFiliusRoot σ m w p GoodIn InPotency
      MoreIn PriorSimply ComponentOf Composite MatterForm Infinite Eternal HasIntellect HasWill
      Pw D' hUnderived hEM hGenus hExisting hEsse hApproach hBeing hPreexist hGoodness
      hTransfer hUniting hKinds hPrior hNoComponent hIntellect hWill hActPrior hNotBoth
      hInfinity hEternity hNaming hGodMaximal (fun _ hx => hx) hLord hPower hImmense
      hIncomprehensible hBlessed
  exact ⟨n, hPerfectRoot, hId, hFirst, hNoMF, hRemote, hGod,
    { one := h.one
      living := hSense n h.immutable (hPureLives n h.immutable)
      creator := h.creator
      lord := h.lord
      almighty := h.almighty
      eternal := h.eternal
      immense := h.immense
      incomprehensible := h.incomprehensible
      intellect := h.intellect
      will := h.will
      perfect := h.perfect
      infinite := h.infinite
      simple := h.simple
      immutable := h.immutable
      spiritual := h.spiritual
      distinct := h.distinct
      blessed := h.blessed
      exalted := h.exalted
      good := h.good }⟩

open TruthCore.Causality.DeiFiliusLivingSelfOperation.Control in
/-- The interpretations and the general fact of `Control.Controls`, checked by unfolding. -/
theorem controls : Controls :=
  ⟨⟨fun _ _ => ⟨(), trivial⟩, fun _ _ _ => trivial, ⟨true, fun _ h => h, trivial⟩⟩,
    ⟨fun _ _ => ⟨(), trivial⟩, fun h => h true (fun _ h => h) ⟨(), trivial⟩,
      ⟨true, fun _ h => h, ⟨(), trivial⟩, fun h => h⟩⟩,
    ⟨fun h => (h true (fun _ h => h)).elim (fun _ h => h),
      fun _ _ ⟨_, h⟩ => h.elim, ⟨true, fun _ h => h, fun h => h⟩⟩,
    ⟨fun _ hp _ => (hp () trivial).elim, fun h => h true ⟨(), trivial⟩⟩,
    ⟨fun _ _ => ⟨(), trivial⟩,
      fun g hp _ => by
        cases g
        · exact (hp () rfl).elim
        · rfl,
      fun h => Bool.false_ne_true (h false trivial)⟩,
    fun _ _ _ _ _ _ h g _ hl => h g hl⟩

end TruthCore.Results.Causality.DeiFiliusLivingSelfOperation
