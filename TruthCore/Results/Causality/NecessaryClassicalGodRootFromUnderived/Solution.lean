module

public import TruthCore.Causality.NecessaryClassicalGodRoot
public import TruthCore.Causality.NecessaryConcreteUnderived
public import TruthCore.Logic.ExcludedMiddle
public import TruthCore.Results.Causality.UnderivedRootPerfection.Solution
public import TruthCore.Results.Causality.PerfectRootPositiveIntellectWill.Solution
public import TruthCore.Results.Causality.ClassicalGodFromPositiveRoot.Solution

/-! Modal spine, the join to stage two. The ungrounded necessary concrete
individual of the join (`NecessaryConcreteUnderivedAt`) is the root the
stage-two attribute chain starts from: one Lean term carries the SAME witness
through `UnderivedRootPerfection`, `PerfectRootPositiveIntellectWill` and
`ClassicalGodFromPositiveRoot` to `NecessaryClassicalGodRootAt`, with no regress
premise (population, whole-roster nontrapping, contingent grounding). Every
attribute, act/being and naming premise stays an explicit open input.

This theorem is registered through `Registration.derive` (result
57213a13-fda3-4d8d-86ec-7f4462a3e7a1), which binds act priority through the
transparent wrapper `IndependentPriority` and delegates here. The statement-level
route this theorem composes already exists through the three registered results
above. Sense-link cleanup that allowed registration: attempt
a062ed2b-028c-40b3-928b-12925a28a261 and docs/notes/modal-spine.md, "The join". -/

@[expose] public section

namespace TruthCore.Results.Causality.NecessaryClassicalGodRootFromUnderived
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic

/-- Compose the join's output with the stage-two attribute chain on ONE model,
world, q3 profile and dictionary. The underived witness's all-world support
exclusion is used only at `w` (inside `UnderivedRootPerfection`). Uniqueness is
among selected actual concrete roots, not all necessary individuals. -/
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
    (hActPrior : ActSimplyPriorToPotencyReading p.InAct InPotency PriorSimply)
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
  have hPerfect :=
    TruthCore.Results.Causality.UnderivedRootPerfection.derive
      m w p.InAct MoreIn p.CausesIn p.esse hUnderived hEM hGenus hExisting hEsse
      hApproach hBeing hPreexist
  have hPositive :=
    TruthCore.Results.Causality.PerfectRootPositiveIntellectWill.derive
      m w p GoodIn MoreIn PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill
      hPerfect hEM hGenus hEsse hBeing hGoodness hTransfer hUniting hKinds hPrior
      hNoComponent hIntellect hWill
  exact TruthCore.Results.Causality.ClassicalGodFromPositiveRoot.derive
    σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf Composite MatterForm
    Infinite Eternal HasIntellect HasWill hPositive hEM hGenus hEsse hActPrior hNotBoth
    hInfinity hEternity hNaming hGodMaximal hSuffice
end TruthCore.Results.Causality.NecessaryClassicalGodRootFromUnderived
