import TruthCore.Causality.DeiFiliusUnifiedRoute
import TruthCore.Results.Causality.DeiFiliusAttributeField.Solution
import TruthCore.Results.Causality.NecessaryClassicalGodRootControl.Solution

/-! The unified Dei Filius route: the restated sufficiency and the Dei Filius root
with every primitive through its typed sense and sense bridge at once, the
derivation of `CausedIsNotInfinite` from the reception-limitation premises, and
two joint-satisfiability models. Analyst formulations, attribution deferred. No
premise is established. -/

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
open TruthCore.Causality.DeiFiliusUnifiedRoute (CausedEsseIsReceived)
open TruthCore.Causality.ReceptionLimitation (ReceivedEsseIsLimited InfiniteEsseIsUnlimited)
open TruthCore.Causality.NamingVeracityBatch1 (Power InfiniteActHasInfinitePower)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic

/-- What has its being caused by another is not INFINITE_1, from one explicit
open bridge and two existing open premises: x, caused in being by some c ≠ x, has
its esse received in some principle (the bridge); received esse is limited; an
INFINITE_1 being's esse is not limited. -/
theorem causedIsNotInfiniteFromReception {B R P : Type}
    (CausesIn : B → B → R → Prop) (esse : R) (Infinite EsseLimited : B → Prop)
    (EsseReceivedIn : B → P → Prop)
    (hReceived : CausedEsseIsReceived CausesIn esse EsseReceivedIn)
    (hLimited : ReceivedEsseIsLimited EsseLimited EsseReceivedIn)
    (hUnlimited : InfiniteEsseIsUnlimited EsseLimited Infinite) :
    CausedIsNotInfinite CausesIn esse Infinite := by
  sorry

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
  sorry

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
  sorry

open TruthCore.Causality.DeiFiliusUnifiedRoute.Control
open TruthCore.Causality.RootPositiveIntellectWillControl (model)
open TruthCore.Causality.NecessaryClassicalGodRootControl (signature)

/-- The controls of `Control.Controls`, checked on the two explicit
interpretations. -/
theorem controls : TruthCore.Causality.DeiFiliusUnifiedRoute.Control.Controls := by
  sorry

end TruthCore.Results.Causality.DeiFiliusUnifiedRoute
