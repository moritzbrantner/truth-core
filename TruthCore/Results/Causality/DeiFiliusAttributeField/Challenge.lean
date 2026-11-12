import TruthCore.Causality.DeiFiliusAttributeField
import TruthCore.Results.Causality.NecessaryClassicalGodRootFromUnderived.Registration.Solution

/-! The stage-two sufficiency premise restated against the defined Dei Filius
attributes (`DeiFiliusAttributeField`). Analyst formulations, attribution
deferred. No premise is established; each theorem is a conditional
consequence of its listed hypotheses. -/

namespace TruthCore.Results.Causality.DeiFiliusAttributeField

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Causality.DeiFiliusAttributeField
open TruthCore.Causality.NamingVeracityBatch1 (Power InfiniteActHasInfinitePower)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic

/-- The nine stage-two attributes give every Dei Filius attribute, from seven
open bridges and three existing premises. Ten conjuncts are the nine
themselves; `creator` unfolds the goodness conjunct (supreme goodness includes
causing every perfection of everything else, so in particular its being);
`spiritual` uses the matter-form clause of the q.3 a.7 composition premise and
simplicity; `exalted` uses goodness-is-actuality (for act as to being) and the
excess-in-act bridge against universal perfection; `almighty` uses the existing
infinite-power premise; `living`, `lord`, `immense`, `incomprehensible`,
`blessed` and `distinct` use one open bridge each. -/
theorem nineGiveDeiFilius (σ : Signature) {Principle Respect : Type}
    (InAct GoodIn InPotency : σ.Being → Respect → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (MoreIn : Respect → σ.Being → σ.Being → Prop) (ComponentOf : σ.Being → σ.Being → Prop)
    (essenceOf esseOf : σ.Being → Principle)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (P : Power σ) (D : Primitives σ.Being)
    (hLiving : IntellectualIsLiving HasIntellect D)
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
  sorry

/-- The old sufficiency premise from the restated one and the field
interpretation: compose the two one-way implications at each being. -/
theorem classicalAttributesSufficeOfDeiFilius (σ : Signature) {Respect : Type}
    (InAct GoodIn InPotency : σ.Being → Respect → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (MoreIn : Respect → σ.Being → σ.Being → Prop) (ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (P : Power σ) (D : Primitives σ.Being)
    (hNine : NineSufficeForDeiFilius σ InAct GoodIn InPotency CausesIn esse MoreIn ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill P D)
    (hField : FieldFromDeiFilius σ InAct GoodIn InPotency CausesIn esse MoreIn ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill P D) :
    ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect InAct)
      (IsSupremelyGood InAct GoodIn CausesIn esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill := by
  sorry

/-- The spine's root with the defined Dei Filius attributes, from the inputs of
the registered join-to-stage-two composition (result 57213a13) WITHOUT the
sufficiency premise, plus six open bridges. The registered composition is
reused on the signature that agrees with `σ` except that its primitive field is
everywhere true (so its sufficiency premise holds trivially there, and nothing
about the field is used); its root then has every Dei Filius attribute:
`distinct`, `spiritual` and `exalted` come from the root's remoteness,
matter-form exclusion and maximum in being, `creator` from its supreme
goodness, `almighty` from infinity through the existing infinite-power premise,
and the five primitives from one bridge each. -/
theorem deiFiliusRoot {W Principle Respect : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being Principle Respect)
    (GoodIn InPotency : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (Pw : Power σ) (D : Primitives σ.Being)
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
    (hLiving : IntellectualIsLiving HasIntellect D)
    (hLord : CreatorOfAllIsLord p.InAct p.CausesIn p.esse D)
    (hPower : InfiniteActHasInfinitePower σ Infinite Pw)
    (hImmense : CreatorOfAllIsImmense p.InAct p.CausesIn p.esse D)
    (hIncomprehensible : InfiniteIsIncomprehensible Infinite D)
    (hBlessed : PerfectIntellectualIsMostBlessed p.InAct HasIntellect D) :
    NecessaryDeiFiliusGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill Pw D := by
  sorry

/-- The old endpoint from the defined one and the field interpretation: the
nine are among the Dei Filius attributes, and the field interpretation gives
the primitive field at the same witness. -/
theorem classicalRootOfDeiFiliusRoot {W Principle Respect : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being Principle Respect)
    (GoodIn InPotency : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (Pw : Power σ) (D : Primitives σ.Being)
    (hRoot : NecessaryDeiFiliusGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill Pw D)
    (hField : FieldFromDeiFilius σ p.InAct GoodIn InPotency p.CausesIn p.esse MoreIn ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill Pw D) :
    NecessaryClassicalGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill := by
  sorry

/-- The controls of `Control.Controls`, checked by unfolding the one-being
interpretations. -/
theorem controls : Control.Controls := by
  sorry

end TruthCore.Results.Causality.DeiFiliusAttributeField
