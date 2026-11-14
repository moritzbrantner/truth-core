module

public import TruthCore.Results.Causality.NecessaryClassicalGodRootFromUnderived.Solution
public import TruthCore.Results.Causality.ClassicalGodFromPositiveRoot.Solution
public import TruthCore.Results.Causality.ActPriorityAtFirst.Solution
public import TruthCore.Causality.ActPriorityThetaEight

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

@[expose] public section

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
theorem pureActOfSimpleExistent {W B R : Type} (o : Ontic W B) (w : W)
    (InAct InPotency : B → R → Prop) (esse : R) (Composite : B → Prop)
    (hExisting : ExistingInActAt o InAct esse w)
    (hComposite : ActInBeingAndPotencyMakeComposite InAct InPotency esse Composite)
    (n : B) (hExists : o.ExistsAt w n) (hSimple : IsSimple Composite n) :
    PureAct InPotency n :=
  fun r hPot => hSimple (hComposite n r (hExisting n hExists) hPot)

/- Non-corpus helper (Solution only, not in the Challenge): the
`ClassicalGodFromPositiveRoot` assembly as restated in
`NecessaryClassicalGodRootAtFirst.classicalGodFromPositiveRootAtFirst`, whose
only change is that the root's pure actuality comes from
`pureActOfSimpleExistent` applied to the root's existence at `w` and its
simplicity. It is restated rather than imported (invariant 17) because the
existing assemblies take act priority and non-overlap as hypotheses, which this
route does not supply. -/
theorem classicalGodFromPositiveRootByComposition {W Principle Respect : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being Principle Respect)
    (GoodIn InPotency : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (hPositiveRoot : TruthCore.Causality.RootPositiveIntellectWill.NecessaryPositiveRootIntellectWillAt
      m w p GoodIn MoreIn PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill)
    (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading p.InAct MoreIn p.CausesIn p.esse)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
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
  obtain ⟨n, hPositive, hGood, hIdentity, hSimple, hFirst, hMatter, hRemote, hInt, hWillN⟩ :=
    hPositiveRoot
  have hMax := hPositive.2.2.2.1
  have hIdent : ∀ y, IsMaximumIn p.InAct MoreIn p.esse y → y = n := by
    intro y hy
    rcases hEM (y = n) with hEq | hNe
    · exact hEq
    · have hCause := hGenus y hy n (fun h => hNe h.symm) hMax.1
      exact (hPositive.1.2 y (hEsse y n hNe hPositive.1.1 hCause)).elim
  have hGod : σ.IsGod n :=
    hNaming n hMax (hGenus n hMax) hGood.2 hRemote hIdent
  have hOne : IsTheOneGod σ.IsGod n := fun g hg => hIdent g (hGodMaximal g hg)
  have hPure : PureAct InPotency n :=
    pureActOfSimpleExistent m.ontic w p.InAct InPotency p.esse Composite hExisting
      hComposite n hPositive.1.1.2 hSimple
  have hInfinite := hInfinity n hIdentity
  have hEternal := hEternity n hPure
  have hNine : NineClassicalAttributes (IsSimple Composite) (IsPerfect p.InAct)
      (IsSupremelyGood p.InAct GoodIn p.CausesIn p.esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill n :=
    ⟨hSimple, hPositive.2.2.2.2, hGood, hOne, hInfinite, hPure, hEternal, hInt, hWillN⟩
  have hField := classicalAttributesFromNine σ (IsSimple Composite) (IsPerfect p.InAct)
    (IsSupremelyGood p.InAct GoodIn p.CausesIn p.esse) (IsTheOneGod σ.IsGod)
    Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill hSuffice n hNine
  exact ⟨n, hPositive, hIdentity, hFirst, hMatter, hRemote, hGod, hNine, hField⟩

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
  have hPerfect :=
    TruthCore.Results.Causality.UnderivedRootPerfection.derive
      m w p.InAct MoreIn p.CausesIn p.esse hUnderived hEM hGenus hExisting hEsse
      hApproach hBeing hPreexist
  have hPositive :=
    TruthCore.Results.Causality.PerfectRootPositiveIntellectWill.derive
      m w p GoodIn MoreIn PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill
      hPerfect hEM hGenus hEsse hBeing hGoodness hTransfer hUniting hKinds hPrior
      hNoComponent hIntellect hWill
  exact classicalGodFromPositiveRootByComposition σ m w p GoodIn InPotency MoreIn PriorSimply
    ComponentOf Composite MatterForm Infinite Eternal HasIntellect HasWill hPositive hEM
    hGenus hExisting hEsse hComposite hInfinity hEternity hNaming hGodMaximal hSuffice

namespace Control

/-! Finite controls on the replaced step only (not on the 22-premise bundle).
Beings and respects are `Bool`: the being `true` is the root, `false` another
being; the respect `true` is being (`esse`), `false` a place. Each control
witnesses one stated interpretation; none shows a premise false or doubtful. -/

open TruthCore.Causality.ActPriorityAtFirst (FirstBeingActPriority)

/-- In act exactly in being. -/
def esseAct (_ : Bool) (r : Bool) : Prop := r = true
/-- In potency exactly to the place. -/
def placePotency (_ : Bool) (r : Bool) : Prop := r = false
/-- Only the other being is in potency, to the place. -/
def otherPlacePotency (x : Bool) (r : Bool) : Prop := x = false ∧ r = false
/-- The root is in act in every respect, the other being in being only. -/
def rootFullAct (x : Bool) (r : Bool) : Prop := r = true ∨ x = true
/-- Nothing is composite. -/
def noComposite (_ : Bool) : Prop := False
/-- Everything is composite. -/
def allComposite (_ : Bool) : Prop := True
/-- Only the other being is composite. -/
def otherComposite (x : Bool) : Prop := x = false
/-- Nothing is simply prior to anything. -/
def noPrior (_ _ : Bool) : Prop := False
/-- The root is simply prior to the other being. -/
def rootPrior (y x : Bool) : Prop := y = true ∧ x = false

/-- Omission (the simple-being-with-an-unrealized-capacity reading): every
being is in act in being, the root is simple and in potency to a place. Non-overlap
holds; the composition premise fails, and so does act priority at a first being:
this reading denies the replaced pair at the root just as it denies the
composition premise, so it rejects the root's pure actuality on both routes. -/
def SimplePotentRoot : Prop :=
  (∀ x, esseAct x true) ∧ IsSimple noComposite true ∧
  NotActAndPotencyInSameRespectReading esseAct placePotency ∧
  ¬ ActInBeingAndPotencyMakeComposite esseAct placePotency true noComposite ∧
  ¬ FirstBeingActPriority esseAct placePotency noPrior ∧
  ¬ PureAct placePotency true

/-- Nonvacuity of the step: the composition premise holds with a being that is
in act in being and in potency (the composite other being), and the simple root
is pure act. -/
def NonvacuousStep : Prop :=
  ActInBeingAndPotencyMakeComposite esseAct otherPlacePotency true otherComposite ∧
  esseAct false true ∧ otherPlacePotency false false ∧
  IsSimple otherComposite true ∧ PureAct otherPlacePotency true

/-- The composition premise and non-overlap do not give act priority at a
first being: a composite first being in potency to a place. At the root the
routes converge only because the root is simple. -/
def CompositionWithoutPriority : Prop :=
  ActInBeingAndPotencyMakeComposite esseAct placePotency true allComposite ∧
  NotActAndPotencyInSameRespectReading esseAct placePotency ∧
  ¬ FirstBeingActPriority esseAct placePotency noPrior

/-- Act priority at a first being and non-overlap do not give the composition
premise: a simple non-first being in act in being and in potency to a place. -/
def PriorityWithoutComposition : Prop :=
  FirstBeingActPriority rootFullAct otherPlacePotency rootPrior ∧
  NotActAndPotencyInSameRespectReading rootFullAct otherPlacePotency ∧
  ¬ ActInBeingAndPotencyMakeComposite rootFullAct otherPlacePotency true noComposite

theorem simplePotentRoot : SimplePotentRoot := by
  unfold SimplePotentRoot IsSimple NotActAndPotencyInSameRespectReading
    ActInBeingAndPotencyMakeComposite FirstBeingActPriority IsFirstBeing PureAct
    esseAct placePotency noComposite noPrior
  decide

theorem nonvacuousStep : NonvacuousStep := by
  unfold NonvacuousStep ActInBeingAndPotencyMakeComposite IsSimple PureAct
    esseAct otherPlacePotency otherComposite
  decide

theorem compositionWithoutPriority : CompositionWithoutPriority := by
  unfold CompositionWithoutPriority ActInBeingAndPotencyMakeComposite
    NotActAndPotencyInSameRespectReading FirstBeingActPriority IsFirstBeing
    esseAct placePotency allComposite noPrior
  decide

theorem priorityWithoutComposition : PriorityWithoutComposition := by
  unfold PriorityWithoutComposition FirstBeingActPriority IsFirstBeing
    NotActAndPotencyInSameRespectReading ActInBeingAndPotencyMakeComposite
    rootFullAct otherPlacePotency rootPrior noComposite
  decide

end Control

end TruthCore.Results.Causality.NecessaryClassicalGodRootByComposition
