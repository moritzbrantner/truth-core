module

public import TruthCore.Causality.DeiFiliusLivingNineScope
public import TruthCore.Results.Causality.DeiFiliusAttributeField.Solution
public import TruthCore.Results.Causality.SelfOperationLife.Solution

/-! *Vivus* from the nine: the self-operation premises restricted to beings with
the nine, their strength order, and the living routes re-derived from them.
Analyst formulations, attribution deferred. No premise is established. -/

@[expose] public section

namespace TruthCore.Results.Causality.DeiFiliusLivingNineScope

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Causality.DeiFiliusAttributeField
open TruthCore.Causality.DeiFiliusLivingSelfOperation
open TruthCore.Causality.DeiFiliusLivingNineScope
open TruthCore.Causality.SelfOperationLife
open TruthCore.Causality.NamingVeracityBatch1 (Power InfiniteActHasInfinitePower)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic

/-- Strength order: every pure act operates (`STMT-PURE-ACT-OPERATES`), so whatever
has the nine operates, since altogether immutability (the sixth of the nine) is
pure act. -/
theorem nineOperateOfPureActOperates {Being Respect : Type}
    (InAct GoodIn InPotency : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (IsGod Composite Infinite Eternal HasIntellect HasWill : Being → Prop)
    (Operates : Being → Prop)
    (hStrong : PureActOperates InPotency Operates) :
    NineOperate InAct GoodIn InPotency CausesIn esse IsGod Composite Infinite Eternal
      HasIntellect HasWill Operates :=
  fun g h => hStrong g h.2.2.2.2.2.1

/-- Strength order: every pure act lives at some time of the frame
(`STMT-PURE-ACT-LIVES`), so whatever has the nine does. -/
theorem nineLiveOfPureActLives {Being Respect Time : Type}
    (InAct GoodIn InPotency : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (IsGod Composite Infinite Eternal HasIntellect HasWill : Being → Prop)
    (LivesAt : Being → Time → Prop)
    (hStrong : PureActLivesReading InPotency LivesAt) :
    NineLiveSomeTime InAct GoodIn InPotency CausesIn esse IsGod Composite Infinite Eternal
      HasIntellect HasWill LivesAt :=
  fun g h => hStrong g h.2.2.2.2.2.1

/-- Whatever has the nine lives at some time of the frame (LIVING_2), from the
weak operation premise, life as self-operation of what is moved in no respect
(q.18 a.3 co.) and the Prima Via premise that nothing is moved except as in
potency. Composes the registered `pureActLives`
(`PURE-ACT-LIVES-FROM-SELF-OPERATION`) on the beings with the nine (a subtype),
where its operation premise `PureActOperates` follows from the weak one. -/
theorem nineLiveFromSelfOperation {Being Respect Time : Type}
    (InAct GoodIn InPotency MovedIn : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (IsGod Composite Infinite Eternal HasIntellect HasWill : Being → Prop)
    (Operates : Being → Prop) (LivesAt : Being → Time → Prop)
    (hOperates : NineOperate InAct GoodIn InPotency CausesIn esse IsGod Composite Infinite
      Eternal HasIntellect HasWill Operates)
    (hLife : SelfOperatingUnmovedLives Operates MovedIn LivesAt)
    (hMoved : MovedOnlyAsInPotencyReading MovedIn InPotency) :
    NineLiveSomeTime InAct GoodIn InPotency CausesIn esse IsGod Composite Infinite Eternal
      HasIntellect HasWill LivesAt := by
  intro g hNine
  have h := TruthCore.Results.Causality.SelfOperationLife.pureActLives
    (B := {x : Being // HasTheNine InAct GoodIn InPotency CausesIn esse IsGod Composite
      Infinite Eternal HasIntellect HasWill x})
    (fun x r => InPotency x.1 r) (fun x r => MovedIn x.1 r)
    (fun x => Operates x.1) (fun x t => LivesAt x.1 t)
    (fun x _ => hOperates x.1 x.2)
    (fun x hOp hUnmoved => hLife x.1 hOp hUnmoved)
    (fun x r hr => hMoved x.1 r hr)
  exact h ⟨g, hNine⟩ hNine.2.2.2.2.2.1

/-- The restated sufficiency (`NineSufficeForDeiFilius`) with its LIVING_1 conjunct
from the weak, nine-restricted life premise. As in
`nineGiveDeiFiliusLivingFromPureAct` (result `08bf7a13`), the registered
`nineGiveDeiFilius` is applied, without `IntellectualIsLiving`, to the primitives
that agree with `D` except that their `Lives` is `HasIntellect`, and every other
conjunct is carried over. At the being `g` with the nine, `NineLiveSomeTime` gives
life at some time of the frame (LIVING_2); `g` is pure act (its immutability
conjunct), so the restricted sense bridge gives `D.Lives g` (LIVING_1). -/
theorem nineGiveDeiFiliusLivingFromNine (σ : Signature) {Principle Respect Time : Type}
    (InAct GoodIn InPotency : σ.Being → Respect → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (MoreIn : Respect → σ.Being → σ.Being → Prop) (ComponentOf : σ.Being → σ.Being → Prop)
    (essenceOf esseOf : σ.Being → Principle)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (P : Power σ) (D : Primitives σ.Being) (LivesAt : σ.Being → Time → Prop)
    (hNineLive : NineLiveSomeTime InAct GoodIn InPotency CausesIn esse σ.IsGod Composite
      Infinite Eternal HasIntellect HasWill LivesAt)
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
      living := hSense g h.immutable (hNineLive g hNine)
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
conjunct from the weak, nine-restricted life premise. As in
`deiFiliusRootLivingFromPureAct` (result `a159ecaf`), the registered
`deiFiliusRoot` is applied, without `IntellectualIsLiving`, to the primitives
that agree with `D` except that their `Lives` is `HasIntellect`. Its root `n` has
the nine (`nineOfDeiFilius`, a projection; none of the nine is `Lives`), so
`NineLiveSomeTime` gives `n` life at some time (LIVING_2), and the restricted
sense bridge gives `D.Lives n` (LIVING_1). -/
theorem deiFiliusRootLivingFromNine {W Principle Respect Time : Type} (σ : Signature)
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
    (hNineLive : NineLiveSomeTime p.InAct GoodIn InPotency p.CausesIn p.esse σ.IsGod Composite
      Infinite Eternal HasIntellect HasWill LivesAt)
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
      living := hSense n h.immutable (hNineLive n (nineOfDeiFilius σ h))
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

open TruthCore.Causality.DeiFiliusLivingNineScope.Control in
/-- The interpretations of `Control.Controls`, checked by unfolding. -/
theorem controls : Controls := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro g h
    exact h.2.2.2.2.2.2.2.1
  · intro h
    exact Bool.false_ne_true (h false (fun _ h => h))
  · exact ⟨fun h => h, fun _ _ _ => trivial, ⟨trivial, fun _ _ _ _ => trivial⟩, fun _ h => h,
      trivial, fun _ h => h, trivial, rfl, trivial⟩
  · exact fun _ h => h
  · exact Bool.false_ne_true
  · intro h
    exact Bool.false_ne_true h.2.2.2.2.2.2.2.1
  · intro g h
    exact ⟨(), h.2.2.2.2.2.2.2.1⟩
  · intro h
    obtain ⟨_, ht⟩ := h false (fun _ h => h)
    exact Bool.false_ne_true ht
  · exact ⟨true, ⟨fun h => h, fun _ _ _ => trivial, ⟨trivial, fun _ _ _ _ => trivial⟩,
      fun _ h => h, trivial, fun _ h => h, trivial, rfl, trivial⟩, (), rfl⟩
  · intro g h
    exact ⟨(), (h.2.2.2.1 true rfl).symm⟩
  · intro g _ hl
    obtain ⟨_, ht⟩ := hl
    exact ht
  · exact fun _ h => h
  · trivial
  · exact Bool.false_ne_true
  · intro h
    exact Bool.false_ne_true (h false trivial)
  · intro g h
    exact ⟨(), h.2.2.2.2.2.2.2.1⟩
  · exact ⟨fun h => h, fun _ _ _ => trivial, ⟨trivial, fun _ _ _ _ => trivial⟩, fun _ h => h,
      trivial, fun _ h => h, trivial, rfl, trivial⟩
  · exact ⟨(), rfl⟩
  · exact fun h => h

end TruthCore.Results.Causality.DeiFiliusLivingNineScope
