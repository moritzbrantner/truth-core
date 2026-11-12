import TruthCore.Causality.DeiFiliusLordBlessed
import TruthCore.Results.Causality.DeiFiliusAttributeField.Solution
import TruthCore.Results.Causality.DeiFiliusOperationFromIntellect.Solution

/-! *Dominus* and *beatissimus* from the nine: typed sibling readings (LORD_2,
BLESSED_2), their derivation from the nine plus named bridges, the strength order
of the new sense bridges against the old bridges, and the Dei Filius routes
re-derived through them. Analyst formulations, attribution deferred. No premise
is established. -/

namespace TruthCore.Results.Causality.DeiFiliusLordBlessed

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Causality.DeiFiliusAttributeField
open TruthCore.Causality.DeiFiliusLivingNineScope (HasTheNine)
open TruthCore.Causality.DeiFiliusLordBlessed
open TruthCore.Causality.NamingVeracityBatch1 (Power InfiniteActHasInfinitePower)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic

/-- Whatever has the nine is LORD_2. Its creator conjunct is contained by
definition in its supreme goodness (the esse instance of causing every perfection
of everything else). Its governance conjunct: the being has intellect and will
(two of the nine) and causes the being of everything else, so the directing
bridge gives, for each other being in act as to being, an end to which it directs
it, and the q.103 a.3 reading turns directing into governing. -/
theorem nineAreLordByCauseAndGovernment {Being Respect End : Type}
    (InAct GoodIn InPotency : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (IsGod Composite Infinite Eternal HasIntellect HasWill : Being → Prop)
    (Directs : Being → Being → End → Prop) (Governs : Being → Being → Prop)
    (hDirects : UniversalIntellectualCauseDirectsAll InAct CausesIn esse HasIntellect HasWill
      Directs)
    (hGoverns : DirectingToAnEndIsGoverningReading Directs Governs) :
    NineAreLordByCauseAndGovernment InAct GoodIn InPotency CausesIn esse IsGod Composite
      Infinite Eternal HasIntellect HasWill Governs := by
  sorry

/-- Whatever has the nine is BLESSED_2: intellect and universal perfection are
two of the nine, and goodness as to being is the first conjunct of supreme
goodness. Act in understanding: the registered
`intellectualPureActOperatesFromCapacity` (result `c55e2ce2`) is applied
with "operating" read as being in act in understanding, so that its third premise
holds trivially; from intellect as the capacity to understand and that capacity
being exercised or in potency, every intellectual pure act is in act in
understanding, and the being with the nine is pure act (its immutability
conjunct). -/
theorem nineAreBlessedByUnderstanding {Being Respect : Type}
    (InAct GoodIn InPotency CanBe : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse understanding : Respect)
    (IsGod Composite Infinite Eternal HasIntellect HasWill : Being → Prop)
    (hCapacity : TruthCore.Causality.DeiFiliusOperationFromIntellect.IntellectIsCapacityToUnderstand
      HasIntellect CanBe understanding)
    (hExercise :
      TruthCore.Causality.DeiFiliusOperationFromIntellect.UnderstandingCapacityExercisedOrInPotency
        InAct InPotency CanBe understanding) :
    NineAreBlessedByUnderstanding InAct GoodIn InPotency CausesIn esse understanding IsGod
      Composite Infinite Eternal HasIntellect HasWill := by
  sorry

/-- Strength order: the old lord bridge (creator of all is lord) gives the new
sense bridge, whose antecedent contains creatorhood. -/
theorem lordSenseBridgeOfCreatorIsLord {Being Respect : Type} (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (Governs : Being → Being → Prop) (D : Primitives Being)
    (hStrong : CreatorOfAllIsLord InAct CausesIn esse D) :
    CauseAndGovernorOfAllIsLord InAct CausesIn esse Governs D := by
  sorry

/-- Strength order: the old beatitude bridge (the perfect intellectual is most
blessed) gives the new sense bridge, whose antecedent contains perfection and
intellect. -/
theorem blessedSenseBridgeOfPerfectIntellectual {Being Respect : Type}
    (InAct GoodIn : Being → Respect → Prop) (esse : Respect) (HasIntellect : Being → Prop)
    (understanding : Respect) (D : Primitives Being)
    (hStrong : PerfectIntellectualIsMostBlessed InAct HasIntellect D) :
    UnderstandingPerfectIsMostBlessed InAct GoodIn esse understanding HasIntellect D := by
  sorry

/-- The restated sufficiency (`NineSufficeForDeiFilius`) with its lord and
most-blessed conjuncts through LORD_2 and BLESSED_2. The registered
`nineGiveDeiFilius` is applied, without `CreatorOfAllIsLord` and
`PerfectIntellectualIsMostBlessed`, to the primitives that agree with `D` except
that `IsLord` is `IsCreatorOfAll` and `MostBlessed` is perfection with intellect;
those two bridges then hold trivially and nothing about the given `IsLord` and
`MostBlessed` is used. At the being `g` with the nine, the derived LORD_2 and
BLESSED_2 and the two sense bridges give `D.IsLord g` and `D.MostBlessed g`;
every other conjunct is carried over. -/
theorem nineGiveDeiFiliusLordBlessedTyped (σ : Signature) {Principle Respect : Type}
    (InAct GoodIn InPotency : σ.Being → Respect → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (MoreIn : Respect → σ.Being → σ.Being → Prop) (ComponentOf : σ.Being → σ.Being → Prop)
    (essenceOf esseOf : σ.Being → Principle)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (P : Power σ) (D : Primitives σ.Being)
    (Governs : σ.Being → σ.Being → Prop) (understanding : Respect)
    (hNineLord : NineAreLordByCauseAndGovernment InAct GoodIn InPotency CausesIn esse σ.IsGod
      Composite Infinite Eternal HasIntellect HasWill Governs)
    (hNineBlessed : NineAreBlessedByUnderstanding InAct GoodIn InPotency CausesIn esse
      understanding σ.IsGod Composite Infinite Eternal HasIntellect HasWill)
    (hLordSense : CauseAndGovernorOfAllIsLord InAct CausesIn esse Governs D)
    (hBlessedSense : UnderstandingPerfectIsMostBlessed InAct GoodIn esse understanding
      HasIntellect D)
    (hLiving : IntellectualIsLiving HasIntellect D)
    (hPower : InfiniteActHasInfinitePower σ Infinite P)
    (hImmense : CreatorOfAllIsImmense InAct CausesIn esse D)
    (hIncomprehensible : InfiniteIsIncomprehensible Infinite D)
    (hNoComponent : CreatorOfAllIsNoComponent InAct CausesIn esse ComponentOf)
    (hExcess : ExcessInBeingIsExcessInAct InAct MoreIn esse)
    (hGoodness : GoodnessIsActualityReading GoodIn InAct)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite essenceOf esseOf) :
    NineSufficeForDeiFilius σ InAct GoodIn InPotency CausesIn esse MoreIn ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill P D := by
  sorry

/-- The spine's root has every typed Dei Filius attribute, with its lord and
most-blessed conjuncts through LORD_2 and BLESSED_2. The registered
`deiFiliusRoot` is applied, without `CreatorOfAllIsLord` and
`PerfectIntellectualIsMostBlessed`, to the same modified primitives as above. Its
root `n` has the nine (`nineOfDeiFilius`, a projection; none of the nine is a
primitive), so the derived LORD_2 and BLESSED_2 hold at `n`, and the sense
bridges give `D.IsLord n` and `D.MostBlessed n`. -/
theorem deiFiliusRootLordBlessedTyped {W Principle Respect : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being Principle Respect)
    (GoodIn InPotency : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (Pw : Power σ) (D : Primitives σ.Being) (Governs : σ.Being → σ.Being → Prop)
    (understanding : Respect)
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
    (hNineLord : NineAreLordByCauseAndGovernment p.InAct GoodIn InPotency p.CausesIn p.esse
      σ.IsGod Composite Infinite Eternal HasIntellect HasWill Governs)
    (hNineBlessed : NineAreBlessedByUnderstanding p.InAct GoodIn InPotency p.CausesIn p.esse
      understanding σ.IsGod Composite Infinite Eternal HasIntellect HasWill)
    (hLordSense : CauseAndGovernorOfAllIsLord p.InAct p.CausesIn p.esse Governs D)
    (hBlessedSense : UnderstandingPerfectIsMostBlessed p.InAct GoodIn p.esse understanding
      HasIntellect D)
    (hLiving : IntellectualIsLiving HasIntellect D)
    (hPower : InfiniteActHasInfinitePower σ Infinite Pw)
    (hImmense : CreatorOfAllIsImmense p.InAct p.CausesIn p.esse D)
    (hIncomprehensible : InfiniteIsIncomprehensible Infinite D) :
    NecessaryDeiFiliusGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill Pw D := by
  sorry

open TruthCore.Causality.DeiFiliusLordBlessed.Control in
open TruthCore.Causality.DeiFiliusLivingNineScope.Control in
/-- The interpretations of `Control.Controls`, checked by unfolding. -/
theorem controls : TruthCore.Causality.DeiFiliusLordBlessed.Control.Controls := by
  sorry

end TruthCore.Results.Causality.DeiFiliusLordBlessed
