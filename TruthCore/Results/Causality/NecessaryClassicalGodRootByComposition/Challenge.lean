import TruthCore.Results.Causality.NecessaryClassicalGodRootFromUnderived.Solution
import TruthCore.Results.Causality.ClassicalGodFromPositiveRoot.Solution
import TruthCore.Results.Causality.ActPriorityAtFirst.Solution
import TruthCore.Causality.ActPriorityThetaEight

/-! Composition sibling of the root's pure actuality (#1603).

The join-to-stage-two composition (`NecessaryClassicalGodRootFromUnderived.Registration.derive`,
argument 8f956c81) and its weak sibling (`NecessaryClassicalGodRootAtFirst.derive`,
argument 69affa96) obtain the root's pure actuality from act priority (over every
potency, or at a first being only) together with same-respect non-overlap,
applied to the root's firstness. This sibling uses neither. It takes the OPEN
composition premise `ActInBeingAndPotencyMakeComposite` (statement d8024a38):
whatever is in act in being and in potency in some respect is composite. The
root `n` exists at `w`, so `ExistingInActAt` (already a premise of the
composition) makes it in act in being; it is simple, which the positive root
already proves from `CompositeHasAUnitingCauseReading` and
`EsseCauseIsActualConcreteGround`; so it is in potency in no respect.

The same `Composite` parameter occurs in the uniting-cause premise, the
matter-form/esse-essence premise, the composition premise and the conclusion's
`IsSimple Composite`, and both premise statements about it link the one
inclusive SIMPLE_4 definition; the same free `InPotency` parameter (POTENCY_2)
occurs in the composition premise, the eternity premise and the conclusion.
Every other premise is the same statement with the same parameters as in the
weak sibling. No premise is discharged. -/

namespace TruthCore.Results.Causality.NecessaryClassicalGodRootByComposition
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Causality.ActPriorityThetaEight (ActInBeingAndPotencyMakeComposite)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic
open TruthCore.German.Kant.CosmologicalInference (Ontic)

/- Non-corpus helper (Solution only): an existent at `w` that is simple is in
potency in no respect, given that existents at `w` are in act in being and the
composition premise. It uses no firstness, act priority or non-overlap. -/

/- Non-corpus helper (Solution only, not in the Challenge): the
`ClassicalGodFromPositiveRoot` assembly as restated in
`NecessaryClassicalGodRootAtFirst.classicalGodFromPositiveRootAtFirst`, whose
only change is that the root's pure actuality comes from
`pureActOfSimpleExistent` applied to the root's existence at `w` and its
simplicity. It is restated rather than imported (invariant 17) because the
existing assemblies take act priority and non-overlap as hypotheses, which this
route does not supply. -/

/-- Sibling of `NecessaryClassicalGodRootAtFirst.derive` with the composition
premise (d8024a38) in place of act priority at a first being (61ad11f3) and
same-respect non-overlap (c6d6379b). Same composition: underived-root
perfection, the positive intellect-will root, then the classical-attribute
assembly above. -/
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
    (hComposite : ActInBeingAndPotencyMakeComposite p.InAct InPotency p.esse Composite)
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

namespace Control

/-! Finite controls on the replaced step only (not on the 22-premise bundle).
Beings and respects are `Bool`: the being `true` is the root, `false` another
being; the respect `true` is being (`esse`), `false` a place. Each control
witnesses one stated interpretation; none shows a premise false or doubtful. -/

open TruthCore.Causality.ActPriorityAtFirst (FirstBeingActPriority)

end Control

end TruthCore.Results.Causality.NecessaryClassicalGodRootByComposition
