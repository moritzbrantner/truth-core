import TruthCore.Causality.DeiFiliusImmenseIncomprehensible
import TruthCore.Results.Causality.DeiFiliusAttributeField.Solution

/-! *Immensus* and *incomprehensibilis* from the nine: typed sibling readings
(IMMENSE_2, INCOMPREHENSIBLE_2), their derivation from the nine plus named
bridges, the strength order of the new sense bridges against the old bridges, and
the Dei Filius routes re-derived through them. Analyst formulations, attribution
deferred. No premise is established. -/

namespace TruthCore.Results.Causality.DeiFiliusImmenseIncomprehensible

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Causality.DeiFiliusAttributeField
open TruthCore.Causality.DeiFiliusLivingNineScope (HasTheNine)
open TruthCore.Causality.DeiFiliusImmenseIncomprehensible
open TruthCore.Causality.NamingVeracityBatch1 (Power InfiniteActHasInfinitePower)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic

/-- Whatever has the nine is IMMENSE_2, with no premise: infinity is one of the
nine, and the creator conjunct is contained by definition in supreme goodness
(its esse instance of causing every perfection of everything else). -/
theorem nineAreImmenseAsInfiniteCauseOfAll {Being Respect : Type}
    (InAct GoodIn InPotency : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (IsGod Composite Infinite Eternal HasIntellect HasWill : Being → Prop) :
    NineAreImmenseAsInfiniteCauseOfAll InAct GoodIn InPotency CausesIn esse IsGod Composite
      Infinite Eternal HasIntellect HasWill := by
  sorry

/-- Whatever has the nine is INCOMPREHENSIBLE_2: it is infinite (one of the nine);
any caused intellect is not infinite (first bridge), so it does not comprehend
the infinite being (second bridge). -/
theorem nineAreIncomprehensibleToCausedIntellects {Being Respect : Type}
    (InAct GoodIn InPotency : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (IsGod Composite Infinite Eternal HasIntellect HasWill : Being → Prop)
    (C : Comprehension Being)
    (hCaused : CausedIsNotInfinite CausesIn esse Infinite)
    (hFinite : FiniteIntellectDoesNotComprehendInfinite Infinite HasIntellect C) :
    NineAreIncomprehensibleToCausedIntellects InAct GoodIn InPotency CausesIn esse IsGod
      Composite Infinite Eternal HasIntellect HasWill C := by
  sorry

/-- Strength order: the old immensity bridge (creator of all is immense) gives
the new sense bridge, whose antecedent contains creatorhood. -/
theorem immenseSenseBridgeOfCreatorIsImmense {Being Respect : Type}
    (InAct : Being → Respect → Prop) (CausesIn : Being → Being → Respect → Prop)
    (esse : Respect) (Infinite : Being → Prop) (D : Primitives Being)
    (hStrong : CreatorOfAllIsImmense InAct CausesIn esse D) :
    InfiniteCauseOfAllIsImmense InAct CausesIn esse Infinite D := by
  sorry

/-- Strength order: the old incomprehensibility bridge (the infinite is
incomprehensible) gives the new sense bridge, whose antecedent contains
infinity. -/
theorem incomprehensibleSenseBridgeOfInfinite {Being Respect : Type}
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (Infinite HasIntellect : Being → Prop) (C : Comprehension Being) (D : Primitives Being)
    (hStrong : InfiniteIsIncomprehensible Infinite D) :
    InfiniteUncomprehendedIsIncomprehensible CausesIn esse Infinite HasIntellect C D := by
  sorry

/-- The restated sufficiency (`NineSufficeForDeiFilius`) with its immense and
incomprehensible conjuncts through IMMENSE_2 and INCOMPREHENSIBLE_2. The
registered `nineGiveDeiFilius` is applied, without `CreatorOfAllIsImmense` and
`InfiniteIsIncomprehensible`, to the primitives that agree with `D` except that
`Immense` is `IsCreatorOfAll` and `Incomprehensible` is `Infinite`; those two
bridges then hold trivially and nothing about the given `Immense` and
`Incomprehensible` is used. At the being `g` with the nine, the derived IMMENSE_2
and INCOMPREHENSIBLE_2 and the two sense bridges give `D.Immense g` and
`D.Incomprehensible g`; every other conjunct is carried over. -/
theorem nineGiveDeiFiliusImmenseIncomprehensibleTyped (σ : Signature) {Principle Respect : Type}
    (InAct GoodIn InPotency : σ.Being → Respect → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (MoreIn : Respect → σ.Being → σ.Being → Prop) (ComponentOf : σ.Being → σ.Being → Prop)
    (essenceOf esseOf : σ.Being → Principle)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (P : Power σ) (D : Primitives σ.Being) (C : Comprehension σ.Being)
    (hNineImmense : NineAreImmenseAsInfiniteCauseOfAll InAct GoodIn InPotency CausesIn esse
      σ.IsGod Composite Infinite Eternal HasIntellect HasWill)
    (hNineIncomprehensible : NineAreIncomprehensibleToCausedIntellects InAct GoodIn InPotency
      CausesIn esse σ.IsGod Composite Infinite Eternal HasIntellect HasWill C)
    (hImmenseSense : InfiniteCauseOfAllIsImmense InAct CausesIn esse Infinite D)
    (hIncomprehensibleSense : InfiniteUncomprehendedIsIncomprehensible CausesIn esse Infinite
      HasIntellect C D)
    (hLiving : IntellectualIsLiving HasIntellect D)
    (hLord : CreatorOfAllIsLord InAct CausesIn esse D)
    (hPower : InfiniteActHasInfinitePower σ Infinite P)
    (hBlessed : PerfectIntellectualIsMostBlessed InAct HasIntellect D)
    (hNoComponent : CreatorOfAllIsNoComponent InAct CausesIn esse ComponentOf)
    (hExcess : ExcessInBeingIsExcessInAct InAct MoreIn esse)
    (hGoodness : GoodnessIsActualityReading GoodIn InAct)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite essenceOf esseOf) :
    NineSufficeForDeiFilius σ InAct GoodIn InPotency CausesIn esse MoreIn ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill P D := by
  sorry

/-- The spine's root has every typed Dei Filius attribute, with its immense and
incomprehensible conjuncts through IMMENSE_2 and INCOMPREHENSIBLE_2. The
registered `deiFiliusRoot` is applied, without `CreatorOfAllIsImmense` and
`InfiniteIsIncomprehensible`, to the same modified primitives as above. Its root
`n` has the nine (`nineOfDeiFilius`, a projection; none of the nine is a
primitive), so the derived IMMENSE_2 and INCOMPREHENSIBLE_2 hold at `n`, and the
sense bridges give `D.Immense n` and `D.Incomprehensible n`. -/
theorem deiFiliusRootImmenseIncomprehensibleTyped {W Principle Respect : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being Principle Respect)
    (GoodIn InPotency : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (Pw : Power σ) (D : Primitives σ.Being) (C : Comprehension σ.Being)
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
    (hNineImmense : NineAreImmenseAsInfiniteCauseOfAll p.InAct GoodIn InPotency p.CausesIn p.esse
      σ.IsGod Composite Infinite Eternal HasIntellect HasWill)
    (hNineIncomprehensible : NineAreIncomprehensibleToCausedIntellects p.InAct GoodIn InPotency
      p.CausesIn p.esse σ.IsGod Composite Infinite Eternal HasIntellect HasWill C)
    (hImmenseSense : InfiniteCauseOfAllIsImmense p.InAct p.CausesIn p.esse Infinite D)
    (hIncomprehensibleSense : InfiniteUncomprehendedIsIncomprehensible p.CausesIn p.esse Infinite
      HasIntellect C D)
    (hLiving : IntellectualIsLiving HasIntellect D)
    (hLord : CreatorOfAllIsLord p.InAct p.CausesIn p.esse D)
    (hPower : InfiniteActHasInfinitePower σ Infinite Pw)
    (hBlessed : PerfectIntellectualIsMostBlessed p.InAct HasIntellect D) :
    NecessaryDeiFiliusGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill Pw D := by
  sorry

open TruthCore.Causality.DeiFiliusImmenseIncomprehensible.Control in
open TruthCore.Causality.DeiFiliusLivingNineScope.Control (inAct noPotency isTrue yes no) in
/-- The interpretations of `Control.Controls`, checked by unfolding. -/
theorem controls : TruthCore.Causality.DeiFiliusImmenseIncomprehensible.Control.Controls := by
  sorry

end TruthCore.Results.Causality.DeiFiliusImmenseIncomprehensible
