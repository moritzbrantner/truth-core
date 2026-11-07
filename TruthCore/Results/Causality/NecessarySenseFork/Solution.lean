module

public import TruthCore.Causality.NecessarySenseFork
public import TruthCore.Results.Causality.NecessaryClassicalGodRoot.Solution
public import TruthCore.Results.Case.Catholicism.Skeleton.Solution
public import TruthCore.Causality.CausalPowerConcreteness

/-! Sense fork over "necessary" for the necessary-classical-God route. Every
theorem imports and applies the existing route theorem
(`NecessaryClassicalGodRoot.derive`) and the Kripke axiom theorems of
`TruthCore.Modal.Kripke` / `TruthCore.Modal.Cube`; nothing is restated. -/

@[expose] public section

namespace TruthCore.Results.Causality.NecessarySenseFork
open TruthCore.Modal
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.Round2Grounding
  (NecessityCauseRelataActualConcrete NecessitatedDependsOnItsCause ActualDependenceIsGrounding)
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic
open TruthCore.Logic.CogitoConcrete

/-- Route node, actualist K reading: from the 25 route inputs, one actual root
is box-existent in the Kripke semantics (`□ atom n` at `w`, frame class K),
exists at `w`, is ungrounded, God, the one God, with the classical attributes.
The box is the route's own `NecessaryAt`, by `necessaryAt_iff_boxExistsAt`. -/
theorem rootActualistK {W Principle Respect : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being Principle Respect)
    (GoodIn InPotency : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
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
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill)
    (CN : σ.Being → σ.Being → Prop) :
    NecessaryRootActualistK σ m w CN := by
  have hRoot := TruthCore.Results.Causality.NecessaryClassicalGodRoot.derive
    σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf Composite MatterForm
    Infinite Eternal HasIntellect HasWill hPop hWhole hDep hEM hGenus hExisting hEsse
    hApproach hBeing hPreexist hGoodness hTransfer hUniting hKinds hPrior hNoComponent
    hIntellect hWill hActPrior hNotBoth hInfinity hEternity hNaming hGodMaximal hSuffice
  obtain ⟨n, hPerfect, _, _, _, _, hGod, hNine, hField⟩ := hRoot
  obtain ⟨hActual, hNec, _⟩ := hPerfect
  exact ⟨n, ⟨hActual.1.2, (necessaryAt_iff_boxExistsAt m.ontic w n).mp hNec⟩,
    hActual, hGod, hNine.2.2.2.1, hField⟩

/-! ## Strength order (each a single-premise registration) -/

/-- Actualist K box-existence implies possibilist K box-existence. -/
theorem actualistKToBoxK {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop)
    (h : NecessaryRootActualistK σ m w CN) : NecessaryRootBoxK σ m w CN := by
  obtain ⟨n, ⟨_, hBox⟩, hFacts⟩ := h
  exact ⟨n, hBox, hFacts⟩

/-- De re box-existence of the root implies de dicto necessary existence of
something (`□∃y E y`, actualist inner quantifier). -/
theorem boxKToDeDictoK {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop)
    (h : NecessaryRootBoxK σ m w CN) : NecessaryRootDeDictoK σ m w CN := by
  obtain ⟨n, hBox, hFacts⟩ := h
  exact ⟨n, fun v hv => ⟨n, hBox v hv⟩, hFacts⟩

/-- Box-existence implies the tertia via's "cannot not-be" with possibility
read as the frame's diamond (K duality; the converse needs excluded middle). -/
theorem boxKToTertiaVia {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop)
    (h : NecessaryRootBoxK σ m w CN) : NecessaryRootTertiaVia σ m w CN := by
  obtain ⟨n, hBox, hFacts⟩ := h
  refine ⟨n, ?_, hFacts⟩
  rintro ⟨v, hv, hNot⟩
  exact hNot (hBox v hv)

/-- Necessary per se implies necessary (tertia via). -/
theorem perSeToTertiaVia {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop)
    (h : NecessaryRootPerSe σ m w CN) : NecessaryRootTertiaVia σ m w CN := by
  obtain ⟨n, hPerSe, hFacts⟩ := h
  exact ⟨n, hPerSe.1, hFacts⟩

/-- T box-existence implies actualist box-existence: axiom T
(`axiomT_valid`) on the reflexive frame yields actual existence. -/
theorem boxTToActualistK {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop)
    (h : NecessaryRootBoxT σ m w CN) : NecessaryRootActualistK σ m w CN := by
  obtain ⟨n, ⟨hKT, hBox⟩, hFacts⟩ := h
  have hAt : Holds m.ontic.frame (existenceValuation m.ontic) w (.atom n) :=
    axiomT_valid m.ontic.frame hKT (.atom n) (existenceValuation m.ontic) w hBox
  exact ⟨n, ⟨hAt, hBox⟩, hFacts⟩

/-- S4 box-existence implies T box-existence (S4 frames are reflexive). -/
theorem boxS4ToBoxT {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop)
    (h : NecessaryRootBoxS4 σ m w CN) : NecessaryRootBoxT σ m w CN := by
  obtain ⟨n, ⟨hS4, hBox⟩, hFacts⟩ := h
  exact ⟨n, ⟨hS4.1, hBox⟩, hFacts⟩

/-- KTB box-existence implies T box-existence. -/
theorem boxBToBoxT {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop)
    (h : NecessaryRootBoxB σ m w CN) : NecessaryRootBoxT σ m w CN := by
  obtain ⟨n, ⟨hB, hBox⟩, hFacts⟩ := h
  exact ⟨n, ⟨hB.1, hBox⟩, hFacts⟩

/-- S5 box-existence implies S4 box-existence (`s5_implies_s4`). -/
theorem boxS5ToBoxS4 {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop)
    (h : NecessaryRootBoxS5 σ m w CN) : NecessaryRootBoxS4 σ m w CN := by
  obtain ⟨n, ⟨hS5, hBox⟩, hFacts⟩ := h
  exact ⟨n, ⟨s5_implies_s4 m.ontic.frame hS5, hBox⟩, hFacts⟩

/-- S5 box-existence implies KTB box-existence (`s5_implies_ktb`). -/
theorem boxS5ToBoxB {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop)
    (h : NecessaryRootBoxS5 σ m w CN) : NecessaryRootBoxB σ m w CN := by
  obtain ⟨n, ⟨hS5, hBox⟩, hFacts⟩ := h
  exact ⟨n, ⟨s5_implies_ktb m.ontic.frame hS5, hBox⟩, hFacts⟩

/-- Route node, possibilist K reading (the weakest de re box reading), from
the same 25 route inputs. -/
theorem rootBoxK {W Principle Respect : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being Principle Respect)
    (GoodIn InPotency : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
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
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill)
    (CN : σ.Being → σ.Being → Prop) :
    NecessaryRootBoxK σ m w CN :=
  actualistKToBoxK σ m w CN (rootActualistK σ m w p GoodIn InPotency MoreIn PriorSimply
    ComponentOf Composite MatterForm Infinite Eternal HasIntellect HasWill hPop hWhole hDep hEM hGenus hExisting hEsse
    hApproach hBeing hPreexist hGoodness hTransfer hUniting hKinds hPrior hNoComponent
    hIntellect hWill hActPrior hNotBoth hInfinity hEternity hNaming hGodMaximal hSuffice CN)

/-! ## Per-branch theorems needing a side condition -/

/-- The T branch: K box-existence of the root plus the OPEN reflexivity premise. -/
theorem boxTFromFrame {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop)
    (hK : NecessaryRootBoxK σ m w CN) (hFrame : OnticFrameKT m) :
    NecessaryRootBoxT σ m w CN := by
  obtain ⟨n, hBox, hFacts⟩ := hK
  exact ⟨n, ⟨hFrame, hBox⟩, hFacts⟩

/-- The S4 branch: K box-existence plus the OPEN S4 frame premise. -/
theorem boxS4FromFrame {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop)
    (hK : NecessaryRootBoxK σ m w CN) (hFrame : OnticFrameS4 m) :
    NecessaryRootBoxS4 σ m w CN := by
  obtain ⟨n, hBox, hFacts⟩ := hK
  exact ⟨n, ⟨hFrame, hBox⟩, hFacts⟩

/-- The B branch: K box-existence plus the OPEN KTB frame premise. -/
theorem boxBFromFrame {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop)
    (hK : NecessaryRootBoxK σ m w CN) (hFrame : OnticFrameKTB m) :
    NecessaryRootBoxB σ m w CN := by
  obtain ⟨n, hBox, hFacts⟩ := hK
  exact ⟨n, ⟨hFrame, hBox⟩, hFacts⟩

/-- The S5 branch: K box-existence plus the OPEN S5 frame premise. -/
theorem boxS5FromFrame {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop)
    (hK : NecessaryRootBoxK σ m w CN) (hFrame : OnticFrameS5 m) :
    NecessaryRootBoxS5 σ m w CN := by
  obtain ⟨n, hBox, hFacts⟩ := hK
  exact ⟨n, ⟨hFrame, hBox⟩, hFacts⟩

/-- The per se branch: the root cannot not-be (tertia via node, the weakest
sense that suffices) and is ungrounded; if causes of
necessity are actual concreta (OPEN), the necessitated depends on its cause
(OPEN), and dependence between actual concreta is grounding (OPEN), then a
cause of the root's necessity would be an actual concrete ground of it, which
an actual root lacks. -/
theorem perSeFromGrounding {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) (Dep : σ.Being → σ.Being → Prop)
    (hTertiaNode : NecessaryRootTertiaVia σ m w CN)
    (hRelata : NecessityCauseRelataActualConcrete m w CN)
    (hDepends : NecessitatedDependsOnItsCause CN Dep)
    (hGround : ActualDependenceIsGrounding m w Dep) :
    NecessaryRootPerSe σ m w CN := by
  obtain ⟨n, hTertia, hFacts⟩ := hTertiaNode
  refine ⟨n, ⟨hTertia, ?_⟩, hFacts⟩
  rintro ⟨c, _, hc⟩
  obtain ⟨hcActual, hnActual⟩ := hRelata c n hc
  exact hFacts.1.2 c ⟨hcActual.1, hcActual.2, hGround c n hnActual hcActual (hDepends c n hc)⟩

/-- Per-sense theorem, by cases on the sense: given the root's actualist K
node and the sense's side condition, the node holds in that sense. -/
theorem nodeInSense {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) (Dep : σ.Being → σ.Being → Prop) (s : Sense)
    (hNode : NecessaryRootActualistK σ m w CN)
    (hSupport : SenseSupport s m w CN Dep) : NecessaryRootInSense s σ m w CN := by
  have hK := actualistKToBoxK σ m w CN hNode
  cases s with
  | boxK => exact hK
  | actualistK => exact hNode
  | deDictoK => exact boxKToDeDictoK σ m w CN hK
  | boxT => exact boxTFromFrame σ m w CN hK hSupport
  | boxS4 => exact boxS4FromFrame σ m w CN hK hSupport
  | boxB => exact boxBFromFrame σ m w CN hK hSupport
  | boxS5 => exact boxS5FromFrame σ m w CN hK hSupport
  | tertiaVia => exact boxKToTertiaVia σ m w CN hK
  | perSe => exact perSeFromGrounding σ m w CN Dep (boxKToTertiaVia σ m w CN hK) hSupport.1 hSupport.2.1 hSupport.2.2

/-- The joint fork theorem. From the 25 route inputs, the OPEN coverage
premise (the intended reading is an enumerated sense), the OPEN exclusivity
premise (it selects exactly one), and the OPEN side conditions of the
intended sense: the root is necessary in the one intended sense. Every
branch succeeds given its side condition; disjunctive syllogism over the
finite enum is `nodeInSense`. -/
theorem forkOnIntendedReading {W Principle Respect : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being Principle Respect)
    (GoodIn InPotency : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
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
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill)
    (CN Dep : σ.Being → σ.Being → Prop) (Intended : Sense → Prop)
    (hCover : NecessarySensesExhaustive Intended)
    (hUnique : NecessarySenseUnique Intended)
    (hSupported : IntendedSenseSupported Intended m w CN Dep) :
    NecessaryRootOnIntendedReading Intended σ m w CN := by
  have hNode := rootActualistK σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
    Composite MatterForm Infinite Eternal HasIntellect HasWill hPop hWhole hDep hEM hGenus hExisting hEsse
    hApproach hBeing hPreexist hGoodness hTransfer hUniting hKinds hPrior hNoComponent
    hIntellect hWill hActPrior hNotBoth hInfinity hEternity hNaming hGodMaximal hSuffice CN
  obtain ⟨s, hs⟩ := hCover
  exact ⟨s, ⟨hs, fun t ht => hUnique t s ht hs⟩,
    nodeInSense σ m w CN Dep s hNode (hSupported s hs)⟩

/-- Root route with the sense as a parameter of the necessary root: the root
necessary in the one intended sense, plus the seven stage 3-6 premises, give
Catholicism (phase 1). Only the root facts are consumed in this last step;
necessity is carried by the node. -/
theorem catholicismFromIntendedReading {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) (Intended : Sense → Prop)
    (hRoot : NecessaryRootOnIntendedReading Intended σ m w CN)
    (hRevelation : RevelationPossibleAndRecognizable σ)
    (hJesus : JesusClaimedDivineAuthorityAndRose σ)
    (hFounded : ChristFoundedVisibleChurch σ)
    (hCatholic : ChristsChurchIsCatholicChurch σ)
    (hDivineFounding : BridgeChristsChurchFoundedByGod σ)
    (hOnlyTruth : BridgeGodFoundedAuthorityProposesOnlyTruth σ)
    (hProposes : CatholicChurchDefinitivelyProposesCreed σ) :
    CatholicismTrue σ := by
  obtain ⟨_, _, g, _, _, hg, hOne, hAttributes⟩ := hRoot
  have hAllAttributes : GodHasClassicalAttributes σ := by
    intro other hOther
    have hSame : other = g := hOne other hOther
    exact hSame.symm ▸ hAttributes
  exact TruthCore.Results.Case.Catholicism.Skeleton.catholicismSkeleton σ ⟨g, hg⟩
    hAllAttributes hRevelation hJesus hFounded hCatholic hDivineFounding hOnlyTruth hProposes

/-! ## By-product: halves of the established concreteness commitment

The route's Cogito population step uses one half of the common-ground premise
`OwnerCommitmentAt` (STMT-CAUSAL-POWER-AND-ACTIVITY-REQUIRE-CONCRETENESS). These
are its two conjunct projections, registered as strength order so the
established commitment establishes each half. Not a modal result. -/

/-- The common-ground commitment implies its activity half. -/
theorem ownerCommitmentToCausers {W B : Type}
    (o : TruthCore.German.Kant.CosmologicalInference.Ontic W B) (concrete : B → Prop)
    (hasCausalPower : W → B → Prop) (w : W)
    (h : TruthCore.Causality.CausalPowerConcreteness.OwnerCommitmentAt o concrete hasCausalPower w) :
    TruthCore.Causality.CausalPowerConcreteness.CausersRequireConcreteAt o concrete w := h.2

/-- The common-ground commitment implies its capacity half. -/
theorem ownerCommitmentToPower {W B : Type}
    (o : TruthCore.German.Kant.CosmologicalInference.Ontic W B) (concrete : B → Prop)
    (hasCausalPower : W → B → Prop) (w : W)
    (h : TruthCore.Causality.CausalPowerConcreteness.OwnerCommitmentAt o concrete hasCausalPower w) :
    TruthCore.Causality.CausalPowerConcreteness.PowerRequiresConcreteAt concrete hasCausalPower w := h.1

/-! ## Controls -/

theorem frameSenseLaws : Control.FrameSenseLaws := by
  intro W B o w x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hKT hBox
    exact axiomT_valid o.frame hKT (.atom x) (existenceValuation o) w hBox
  · intro hS4 hBox
    exact axiom4_valid o.frame hS4.2 (.atom x) (existenceValuation o) w hBox
  · intro hKTB hAt
    exact axiomB_valid o.frame hKTB.2 (.atom x) (existenceValuation o) w hAt
  · rintro hS5 ⟨v, hwv, hBoxV⟩ u hwu
    exact hBoxV u (hS5.2 w v u hwv hwu)

theorem certificate : Control.Certificate := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro v hv
    show v < 2
    rcases hv with h | h
    · exact h ▸ (by decide : 0 < 2)
    · exact h ▸ (by decide : 0 + 1 < 2)
  · intro h
    exact Nat.lt_irrefl 2 (h 1 (Or.inr rfl) 2 (Or.inr rfl))
  · intro v hv
    exact hv.2
  · intro h
    exact Bool.noConfusion h
  · intro v _
    exact ⟨v, rfl⟩
  · rintro ⟨y, hy⟩
    cases y with
    | false => exact Bool.noConfusion (hy true trivial)
    | true => exact Bool.noConfusion (hy false trivial)

theorem perSeSeparation : Control.PerSeSeparation := by
  refine ⟨fun _ _ => trivial, ?_, ?_⟩
  · rintro ⟨_, _, h⟩
    exact h trivial
  · rintro ⟨_, hNot⟩
    exact hNot ⟨false, Bool.noConfusion, rfl, rfl⟩

theorem nonvacuity : Control.Nonvacuity := by
  refine ⟨?_, ⟨_, rfl⟩, fun s t hs ht => hs.trans ht.symm⟩
  have hBox : BoxExistsAt Control.unitProfile.ontic () () := fun _ _ => trivial
  have hFacts : RootFacts Control.unitSignature Control.unitProfile () () :=
    ⟨⟨⟨trivial, trivial⟩, fun _ h => h.2.2⟩, trivial, fun _ _ => rfl, trivial⟩
  have hUniv : ∀ a b : Unit, Control.unitProfile.ontic.frame.access a b := fun _ _ => trivial
  have hS5 : FrameSatisfies .S5 Control.unitProfile.ontic.frame :=
    ⟨fun _ => trivial, fun _ _ _ _ _ => trivial⟩
  have hS4 : FrameSatisfies .S4 Control.unitProfile.ontic.frame :=
    ⟨fun _ => trivial, fun _ _ _ _ _ => trivial⟩
  have hKTB : FrameSatisfies .KTB Control.unitProfile.ontic.frame :=
    ⟨fun _ => trivial, fun _ _ _ => trivial⟩
  have hTertia : IsNecessary (FramePossible Control.unitProfile.ontic ())
      (ExistsIndexed Control.unitProfile.ontic) () := by
    rintro ⟨_, _, h⟩
    exact h trivial
  intro s
  cases s with
  | boxK => exact ⟨⟨(), hBox, hFacts⟩, trivial⟩
  | actualistK => exact ⟨⟨(), ⟨trivial, hBox⟩, hFacts⟩, trivial⟩
  | deDictoK => exact ⟨⟨(), fun _ _ => ⟨(), trivial⟩, hFacts⟩, trivial⟩
  | boxT => exact ⟨⟨(), ⟨fun _ => trivial, hBox⟩, hFacts⟩, fun _ => trivial⟩
  | boxS4 => exact ⟨⟨(), ⟨hS4, hBox⟩, hFacts⟩, hS4⟩
  | boxB => exact ⟨⟨(), ⟨hKTB, hBox⟩, hFacts⟩, hKTB⟩
  | boxS5 => exact ⟨⟨(), ⟨hS5, hBox⟩, hFacts⟩, hS5⟩
  | tertiaVia => exact ⟨⟨(), hTertia, hFacts⟩, trivial⟩
  | perSe =>
      exact ⟨⟨(), ⟨hTertia, fun ⟨_, _, h⟩ => h⟩, hFacts⟩,
        fun _ _ h => h.elim, fun _ _ h => h.elim, fun _ _ _ _ h => h.elim⟩

/-- The batch controls, one certificate. -/
theorem controls : Control.Controls :=
  ⟨frameSenseLaws, certificate, perSeSeparation, nonvacuity⟩

end TruthCore.Results.Causality.NecessarySenseFork
