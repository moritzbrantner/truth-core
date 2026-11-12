import TruthCore.Results.Causality.NecessaryClassicalGodRootFromUnderived.Solution
import TruthCore.Results.Causality.ClassicalGodFromPositiveRoot.Solution
import TruthCore.Results.Causality.ActPriorityAtFirst.Solution

/-! Weak-version sibling of the join-to-stage-two composition
(`NecessaryClassicalGodRootFromUnderived.Registration.derive`, argument 8f956c81).

The registered composition takes act's simple priority over every potency of
the independently supplied potency parameter (`IndependentPriority`, statement
3b2d2d46). Its only use is in `ClassicalGodFromPositiveRoot.derive`, where
`firstBeingNoPotency` applies it to the root, which is a first being. This
sibling takes the first-being version `FirstBeingActPriority` (statement
61ad11f3, registered strength order 3b2d2d46 ⇒ 61ad11f3) instead. With the
same non-overlap premise, the existing `ActPriorityAtFirst.facts` (the proof
of `Control.Facts`, item 2) gives that a first being is in potency in no respect. Every other
premise is the same statement with the same parameters, and the same potency
parameter `InPotency` occurs throughout. No premise is discharged. -/

namespace TruthCore.Results.Causality.NecessaryClassicalGodRootAtFirst
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Causality.ActPriorityAtFirst (FirstBeingActPriority)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic

/- Non-corpus helper (Solution only, not in the Challenge): `ClassicalGodFromPositiveRoot.derive` with act priority
required at a first being only. Same assembly; pure actuality of the root comes
from the first-being version and non-overlap (`ActPriorityAtFirst.facts`,
item 2). The assembly is restated rather than imported (invariant 17) because
`ClassicalGodFromPositiveRoot.derive` takes the strong reading as a hypothesis,
and its `InPotency` and `PriorSimply` parameters also occur in its conclusion,
so no instantiation turns the weak version into that hypothesis; the existing
registered module is left unchanged. -/

/-- Sibling of `NecessaryClassicalGodRootFromUnderived.Registration.derive` with
act priority at a first being (61ad11f3) in place of act priority over every
potency (3b2d2d46). Same composition: underived-root perfection, the positive
intellect-will root, then the classical-attribute assembly above. -/
theorem derive {W Principle Respect : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being Principle Respect)
    (GoodIn InPotency : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
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
    (hActPrior : FirstBeingActPriority p.InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading p.InAct InPotency)
    (hInfinity : SubsistentBeingIsInfiniteReading p.essenceOf p.esseOf Infinite)
    (hEternity : ImmutableIsEternalReading InPotency Eternal)
    (hNaming : GodNamesTheFullyDescribedPrinciple p.InAct MoreIn p.CausesIn p.esse ComponentOf σ.IsGod)
    (hGodMaximal : GodIsMaximalInBeing σ.IsGod p.InAct MoreIn p.esse)
    (hSuffice : ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect p.InAct)
      (IsSupremelyGood p.InAct GoodIn p.CausesIn p.esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill) :
    NecessaryClassicalGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill := by
  sorry

end TruthCore.Results.Causality.NecessaryClassicalGodRootAtFirst
